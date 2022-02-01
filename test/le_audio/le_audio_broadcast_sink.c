/*
 * Copyright (C) 2022 BlueKitchen GmbH
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the copyright holders nor the names of
 *    contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 * 4. Any redistribution, use, or modification is done solely for
 *    personal benefit and not for any commercial purpose or for
 *    monetary gain.
 *
 * THIS SOFTWARE IS PROVIDED BY BLUEKITCHEN GMBH AND CONTRIBUTORS
 * ``AS IS'' AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
 * FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL MATTHIAS
 * RINGWALD OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
 * BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS
 * OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED
 * AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF
 * THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * Please inquire about commercial licensing options at 
 * contact@bluekitchen-gmbh.com
 *
 */

#define BTSTACK_FILE__ "le_audio_broadcast_sink.c"

/*
 * LE Audio Broadcast Sink
 */


#include "btstack_config.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <inttypes.h>
#include <fcntl.h>        // open
#include <unistd.h>       // write
#include <errno.h>
#include <bluetooth_gatt.h>

#include "ble/sm.h"
#include "btstack_event.h"
#include "btstack_run_loop.h"
#include "gap.h"
#include "hci.h"
#include "hci_cmd.h"
#include "l2cap.h"
#include "btstack_stdin.h"
#include "ad_parser.h"
#include "bluetooth_data_types.h"
#include "btstack_util.h"

#define DUMP_LEN_S 10
#define MAX_NUM_BIS 2

static bd_addr_t remote;
static bd_addr_type_t remote_type;
static uint8_t remote_sid;

static const uint8_t    big_handle = 1;
static hci_con_handle_t sync_handle;
static hci_con_handle_t bis_con_handles[MAX_NUM_BIS];
static unsigned int     next_bis_index;

static btstack_packet_callback_registration_t hci_event_callback_registration;

static enum {
    APP_W4_WORKING,
    APP_W4_BROADCAST_ADV,
    APP_W4_PA_AND_BIG_INFO,
    APP_CREATE_BIG_SYNC,
    APP_W4_BIG_SYNC_ESTABLISHED,
    APP_SET_ISO_PATHS,
    APP_STREAMING,
    APP_TERMINATE_BIG,
    APP_IDLE
} app_state = APP_W4_WORKING;

static void show_usage(void);

static char remote_name[20];

static bool have_base;
static bool have_big_info;

static int dump_file;
static uint32_t samples;
uint32_t last_samples_report_ms;

static const char * filename = "le_audio_broadcast_sink.lc3";

// codec config
static uint32_t sampling_frequency_hz;
static uint16_t frame_duration_100us;
static uint16_t octets_per_frame;
static uint8_t  num_bis;

static void open_lc3_file(void) {
    // open lc3 file
    int oflags = O_WRONLY | O_CREAT | O_TRUNC;
    dump_file = open(filename, oflags, S_IRUSR | S_IWUSR | S_IRGRP | S_IROTH);
    if (dump_file < 0) {
        printf("failed to open file %s, errno = %d\n", filename, errno);
        return;
    }

    printf("LC3 binary file: %s\n", filename);

    // calc bps
    uint32_t bits_per_second = (uint32_t) octets_per_frame * 8 * 10000 / frame_duration_100us;

    // write header for floating point implementation
    uint8_t header[18];
    little_endian_store_16(header, 0, 0xcc1c);
    little_endian_store_16(header, 2, sizeof(header));
    little_endian_store_16(header, 4, sampling_frequency_hz / 100);
    little_endian_store_16(header, 6, bits_per_second / 100);
    little_endian_store_16(header, 8, num_bis);
    little_endian_store_16(header, 10, frame_duration_100us * 10);
    little_endian_store_16(header, 12, 0);
    little_endian_store_32(header, 14, DUMP_LEN_S * sampling_frequency_hz);
    write(dump_file, header, sizeof(header));
}

static void handle_periodic_advertisement(const uint8_t * packet, uint16_t size){
    // periodic advertisement contains the BASE
    // TODO: BASE might be split across multiple advertisements
    const uint8_t * adv_data = hci_subevent_le_periodic_advertising_report_get_data(packet);
    uint16_t adv_size = hci_subevent_le_periodic_advertising_report_get_data_length(packet);

    ad_context_t context;
    for (ad_iterator_init(&context, adv_size, adv_data) ; ad_iterator_has_more(&context) ; ad_iterator_next(&context)) {
        uint8_t data_type = ad_iterator_get_data_type(&context);
        uint8_t data_size = ad_iterator_get_data_len(&context);
        const uint8_t * data = ad_iterator_get_data(&context);
        uint16_t uuid;
        switch (data_type){
            case BLUETOOTH_DATA_TYPE_SERVICE_DATA_16_BIT_UUID:
                uuid = little_endian_read_16(data, 0);
                if (uuid == ORG_BLUETOOTH_SERVICE_BASIC_AUDIO_ANNOUNCEMENT_SERVICE){
                    have_base = true;
                    // Level 1: Group Level
                    const uint8_t * base_data = &data[2];
                    uint16_t base_len = data_size - 2;
                    printf("BASE:\n");
                    uint32_t presentation_delay = little_endian_read_24(base_data, 0);
                    printf("- presentation delay: %"PRIu32" us\n", presentation_delay);
                    uint8_t num_subgroups = base_data[3];
                    printf("- num subgroups: %u\n", num_subgroups);
                    uint8_t i;
                    uint16_t offset = 4;
                    for (i=0;i<num_subgroups;i++){
                        // Level 2: Subgroup Level
                        num_bis = base_data[offset++];
                        printf("  - num bis[%u]: %u\n", i, num_bis);
                        // codec_id: coding format = 0x06, vendor and coded id = 0
                        offset += 5;
                        uint8_t codec_specific_configuration_length = base_data[offset++];
                        const uint8_t * codec_specific_configuration = &base_data[offset];
                        printf("  - codec specific config[%u]: ", i);
                        printf_hexdump(codec_specific_configuration, codec_specific_configuration_length);
                        // parse config to get sampling frequency and frame duration
                        uint8_t codec_offset = 0;
                        while ((codec_offset + 1) < codec_specific_configuration_length){
                            uint8_t ltv_len = codec_specific_configuration[codec_offset++];
                            uint8_t ltv_type = codec_specific_configuration[codec_offset];
                            const uint32_t sampling_frequency_map[] = { 8000, 11025, 16000, 22050, 24000, 32000, 44100, 48000, 88200, 96000, 176400, 192000, 384000 };
                            uint8_t sampling_frequency_index;
                            uint8_t frame_duration_index;
                            switch (ltv_type){
                                case 0x01: // sampling frequency
                                    sampling_frequency_index = codec_specific_configuration[codec_offset+1];
                                    // TODO: check range
                                    sampling_frequency_hz = sampling_frequency_map[sampling_frequency_index - 1];
                                    printf("  - sampling frequency[%u]: %"PRIu32"\n", i, sampling_frequency_hz);
                                    break;
                                case 0x02: // 0 = 7.5, 1 = 10 ms
                                    frame_duration_index =  codec_specific_configuration[codec_offset+1];
                                    frame_duration_100us = (frame_duration_index == 0) ? 75 : 100;
                                    printf("  - frame duration[%u]: %s ms\n", i, (frame_duration_index == 0) ? "7.5" : "10");
                                    break;
                                case 0x04:  // octets per coding frame
                                    octets_per_frame = little_endian_read_16(codec_specific_configuration, codec_offset+1);
                                    printf("  - octets per codec frame[%u]: %u\n", i, octets_per_frame);
                                    break;
                                default:
                                    break;
                            }
                            codec_offset += ltv_len;
                        }
                        //
                        offset += codec_specific_configuration_length;
                        uint8_t metadata_length = base_data[offset++];
                        const uint8_t * meta_data = &base_data[offset];
                        offset += metadata_length;
                        printf("  - meta data[%u]: ", i);
                        printf_hexdump(meta_data, metadata_length);
                        uint8_t k;
                        for (k=0;k<num_bis;k++){
                            // Level 3: BIS Level
                            uint8_t bis_index = base_data[offset++];
                            printf("    - bis index[%u][%u]: %u\n", i, k, bis_index);
                            uint8_t codec_specific_configuration_length2 = base_data[offset++];
                            const uint8_t * codec_specific_configuration2 = &base_data[offset];
                            printf("    - codec specific config[%u][%u]: ", i, k);
                            printf_hexdump(codec_specific_configuration2, codec_specific_configuration_length2);
                            offset += codec_specific_configuration_length2;
                        }
                    }
                }
                break;
            default:
                break;
        }
    }
}

static void handle_big_info(const uint8_t * packet, uint16_t size){
    printf("BIG Info advertising report\n");
    sync_handle = hci_subevent_le_biginfo_advertising_report_get_sync_handle(packet);
    have_big_info = true;
}

static void enter_create_big_sync(void){
    // stop scanning
    gap_stop_scan();

    // collect data
    open_lc3_file();
    app_state = APP_CREATE_BIG_SYNC;
}

static void packet_handler (uint8_t packet_type, uint16_t channel, uint8_t *packet, uint16_t size){
    UNUSED(channel);
    if (packet_type != HCI_EVENT_PACKET) return;
    unsigned int i;
    switch (packet[0]) {
        case BTSTACK_EVENT_STATE:
            switch(btstack_event_state_get_state(packet)) {
                case HCI_STATE_WORKING:
                    if (app_state != APP_W4_WORKING) break;
                    app_state = APP_W4_BROADCAST_ADV;
                    gap_set_scan_params(1, 0x30, 0x30, 0);
                    gap_start_scan();
                    printf("Start scan..\n");
                    break;
                case HCI_STATE_OFF:
                    printf("Goodbye\n");
                    exit(0);
                    break;
                default:
                    break;
            }
            break;
        case GAP_EVENT_EXTENDED_ADVERTISING_REPORT:
        {
            if (app_state != APP_W4_BROADCAST_ADV) break;

            gap_event_extended_advertising_report_get_address(packet, remote);
            uint8_t adv_size = gap_event_extended_advertising_report_get_data_length(packet);
            const uint8_t * adv_data = gap_event_extended_advertising_report_get_data(packet);

            ad_context_t context;
            bool found = false;
            remote_name[0] = '\0';
            uint16_t uuid;
            for (ad_iterator_init(&context, adv_size, adv_data) ; ad_iterator_has_more(&context) ; ad_iterator_next(&context)) {
                uint8_t data_type = ad_iterator_get_data_type(&context);
                uint8_t size = ad_iterator_get_data_len(&context);
                const uint8_t *data = ad_iterator_get_data(&context);
                switch (data_type){
                    case BLUETOOTH_DATA_TYPE_SERVICE_DATA_16_BIT_UUID:
                        uuid = little_endian_read_16(data, 0);
                        if (uuid == ORG_BLUETOOTH_SERVICE_BROADCAST_AUDIO_ANNOUNCEMENT_SERVICE){
                            found = true;
                        }
                        break;
                    case BLUETOOTH_DATA_TYPE_SHORTENED_LOCAL_NAME:
                    case BLUETOOTH_DATA_TYPE_COMPLETE_LOCAL_NAME:
                        size = btstack_min(sizeof(remote_name) - 1, size);
                        memcpy(remote_name, data, size);
                        remote_name[size] = 0;
                        break;
                    default:
                        break;
                }
            }
            if (!found) break;
            remote_type = gap_event_extended_advertising_report_get_address_type(packet);
            remote_sid = gap_event_extended_advertising_report_get_advertising_sid(packet);
            printf("Remote Broadcast sink found, addr %s, name: '%s'\n", bd_addr_to_str(remote), remote_name);
            // ignore other advertisements
            gap_whitelist_add(remote_type, remote);
            gap_set_scan_params(1, 0x30, 0x30, 1);
            // sync to PA
            gap_periodic_advertiser_list_clear();
            gap_periodic_advertiser_list_add(remote_type, remote, remote_sid);
            app_state = APP_W4_PA_AND_BIG_INFO;
            printf("Start Periodic Advertising Sync\n");
            gap_periodic_advertising_create_sync(0x01, remote_sid, remote_type, remote, 0, 1000, 0);
            break;
        }
        case HCI_EVENT_LE_META:
            switch(hci_event_le_meta_get_subevent_code(packet)) {
                case HCI_SUBEVENT_LE_PERIODIC_ADVERTISING_SYNC_ESTABLISHMENT:
                    printf("Periodic advertising sync established\n");
                    break;
                case HCI_SUBEVENT_LE_PERIODIC_ADVERTISING_REPORT:
                    if (have_base) break;
                    handle_periodic_advertisement(packet, size);
                    if (have_big_info){
                        enter_create_big_sync();
                    }
                    break;
                case HCI_SUBEVENT_LE_BIGINFO_ADVERTISING_REPORT:
                    if (have_big_info) break;
                    handle_big_info(packet, size);
                    if (have_base){
                        enter_create_big_sync();
                    }
                    break;
                case HCI_SUBEVENT_LE_BIG_SYNC_ESTABLISHED:
                    printf("BIG Sync Established\n");
                    if (app_state == APP_W4_BIG_SYNC_ESTABLISHED){
                        gap_stop_scan();
                        gap_periodic_advertising_terminate_sync(sync_handle);
                        // update num_bis
                        num_bis = packet[16];
                        for (i=0;i<num_bis;i++){
                            bis_con_handles[i] = little_endian_read_16(packet, 17 + 2*i);
                        }
                        next_bis_index = 0;
                        app_state = APP_SET_ISO_PATHS;
                    }
                    break;
                default:
                    break;
            }
        default:
            break;
    }

    if (!hci_can_send_command_packet_now()) return;

    const uint8_t broadcast_code[16] = { 0 };
    uint8_t bis_array[MAX_NUM_BIS];
    switch(app_state){
        case APP_CREATE_BIG_SYNC:
            app_state = APP_W4_BIG_SYNC_ESTABLISHED;
            printf("BIG Create Sync for BIS: ");
            for (i=0;i<num_bis;i++){
                bis_array[i] = i + 1;
                printf("%u ", bis_array[i]);
            }
            printf("\n");
            hci_send_cmd(&hci_le_big_create_sync, big_handle, sync_handle, 0, broadcast_code, 0, 100, num_bis, bis_array);
            break;
        case APP_SET_ISO_PATHS:
            hci_send_cmd(&hci_le_setup_iso_data_path, bis_con_handles[next_bis_index++], 1, 0, 0, 0, 0, 0, 0, NULL);
            if (next_bis_index == num_bis){
                app_state = APP_STREAMING;
                last_samples_report_ms = btstack_run_loop_get_time_ms();
            }
            break;
        case APP_TERMINATE_BIG:
            hci_send_cmd(&hci_le_big_terminate_sync, big_handle);
            app_state = APP_IDLE;
            printf("Shutdown...\n");
            hci_power_control(HCI_POWER_OFF);
            break;
        default:
            break;
    }
}

static void iso_packet_handler(uint8_t packet_type, uint16_t channel, uint8_t *packet, uint16_t size){

    if (samples >= (DUMP_LEN_S * sampling_frequency_hz)) {
        return;
    }

    uint16_t header = little_endian_read_16(packet, 0);
    hci_con_handle_t con_handle = header & 0x0fff;
    uint8_t pb_flag = (header >> 12) & 3;
    uint8_t ts_flag = (header >> 14) & 1;
    uint16_t iso_load_len = little_endian_read_16(packet, 2);

    uint16_t offset = 4;
    uint32_t time_stamp = 0;
    if (ts_flag){
        uint32_t time_stamp = little_endian_read_32(packet, offset);
        offset += 4;
    }

    uint16_t packet_sequence_number = little_endian_read_16(packet, offset);
    offset += 2;

    uint16_t header_2 = little_endian_read_16(packet, offset);
    uint16_t iso_sdu_length = header_2 & 0x3fff;
    uint8_t packet_status_flag = (uint8_t) (header_2 >> 14);
    offset += 2;

    if (iso_sdu_length == 0) return;

    // store len header only for first bis
    if (con_handle == bis_con_handles[0]){
        uint8_t len_header[2];
        little_endian_store_16(len_header, 0, num_bis * iso_sdu_length);
        write(dump_file, len_header, 2);
    }

    // store single channel codec frame
    write(dump_file, &packet[offset], iso_sdu_length);

    samples += 80;
    uint32_t time_ms = btstack_run_loop_get_time_ms();
    if (btstack_time_delta(time_ms, last_samples_report_ms) > 1000){
        last_samples_report_ms = time_ms;
        printf("Samples: %6u\n", samples / num_bis);
    }

    if (samples >= (DUMP_LEN_S * sampling_frequency_hz * num_bis)){
        printf("Done, disconnect all BIS\n");
        close(dump_file);
        app_state = APP_TERMINATE_BIG;

        // duplicate from packet handler above
        hci_send_cmd(&hci_le_big_terminate_sync, big_handle);
        app_state = APP_IDLE;
        printf("Shutdown...\n");
        hci_power_control(HCI_POWER_OFF);

    }

//    printf("ISO con %04x, pb_flag %u, ts_flag %u, iso_load_len %3u, ts %10"PRIu32", seq nr: %5u, iso_pdu_len %3u, packet status flag: %u, frag size: %u - ",
//           con_handle, pb_flag, ts_flag, iso_load_len, time_stamp, packet_sequence_number, iso_sdu_length, packet_status_flag, size - offset);
//    printf_hexdump(&packet[offset], size - offset);
}

static void show_usage(void){
    printf("\n--- LE Audio Broadcast Sink Test Console ---\n");
    printf("x or Ctrl-c - exit\n");
    printf("---\n");
}

static void stdin_process(char c){
    switch (c){
        case 'x':
            printf("Shutdown...\n");
            hci_power_control(HCI_POWER_OFF);
            break;
        case '\n':
        case '\r':
            break;
        default:
            show_usage();
            break;

    }
}

int btstack_main(int argc, const char * argv[]);
int btstack_main(int argc, const char * argv[]){
    (void) argv;
    (void) argc;
    
    // register for HCI events
    hci_event_callback_registration.callback = &packet_handler;
    hci_add_event_handler(&hci_event_callback_registration);

    // register for ISO Packet
    hci_register_iso_packet_handler(&iso_packet_handler);

    // turn on!
    hci_power_control(HCI_POWER_ON);

    btstack_stdin_setup(stdin_process);
    return 0;
}
