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

#define BTSTACK_FILE__ "le_audio_broadcast_source.c"

/*
 * LE Audio Broadcast Source
 */


#include "btstack_config.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "ble/sm.h"
#include "btstack_event.h"
#include "btstack_memory.h"
#include "btstack_run_loop.h"
#include "gap.h"
#include "hci.h"
#include "hci_cmd.h"
#include "hci_dump.h"
#include "l2cap.h"
#include "btstack_stdin.h"
#include "bluetooth_data_types.h"

static const uint8_t adv_sid = 0;

static le_advertising_set_t le_advertising_set;

static const le_extended_advertising_parameters_t extended_params = {
        .advertising_event_properties = 0,
        .primary_advertising_interval_min = 0x4b0, // 750 ms
        .primary_advertising_interval_max = 0x4b0, // 750 ms
        .primary_advertising_channel_map = 7,
        .own_address_type = 0,
        .peer_address_type = 0,
        .peer_address = 0,
        .advertising_filter_policy = 0,
        .advertising_tx_power = 10, // 10 dBm
        .primary_advertising_phy = 1, // LE 1M PHY
        .secondary_advertising_max_skip = 0,
        .secondary_advertising_phy = 1, // LE 1M PHY
        .advertising_sid = adv_sid,
        .scan_request_notification_enable = 0,
};

static const uint8_t extended_adv_data[] = {
        // 16 bit service data, ORG_BLUETOOTH_SERVICE_BASIC_AUDIO_ANNOUNCEMENT_SERVICE, Broadcast ID
        6, BLUETOOTH_DATA_TYPE_SERVICE_DATA_16_BIT_UUID, 0x52, 0x18, 0x30, 0x5d, 0x9b,
        // name
        7, BLUETOOTH_DATA_TYPE_COMPLETE_LOCAL_NAME, 'S', 'o', 'u', 'r', 'c', 'e'
};

static const le_periodic_advertising_parameters_t periodic_params = {
        .periodic_advertising_interval_min = 0x258, // 375 ms
        .periodic_advertising_interval_max = 0x258, // 375 ms
        .periodic_advertising_properties = 0
};

static const uint8_t periodic_adv_data[] = {
    // 16 bit service dat
    7, BLUETOOTH_DATA_TYPE_SERVICE_DATA_16_BIT_UUID, 0x51, 0x18, 0x00, 0x01, 0x02, 0x03 // TODO setup periodic adv data
};

static bd_addr_t remote;
static const char * remote_addr_string = "00:1B:DC:08:E2:72";

static btstack_packet_callback_registration_t hci_event_callback_registration;

static uint8_t adv_handle = 0;
static hci_con_handle_t big_con_handle;

static enum {
    APP_W4_PERIODIC_ENABLED,
    APP_CREATE_BIG,
    APP_W4_BIG_CON_HANDLE,
    APP_SET_ISO_PATH,
    APP_IDLE
} app_state = APP_W4_PERIODIC_ENABLED;

static void show_usage(void);

static void packet_handler (uint8_t packet_type, uint16_t channel, uint8_t *packet, uint16_t size){
    UNUSED(channel);
    if (packet_type != HCI_EVENT_PACKET) return;

    switch (packet[0]) {
        case HCI_EVENT_COMMAND_COMPLETE:
            if (hci_event_command_complete_get_command_opcode(packet) == hci_le_set_periodic_advertising_enable.opcode){
                if (app_state != APP_W4_PERIODIC_ENABLED) break;
                app_state = APP_CREATE_BIG;
            }
            break;
        case HCI_EVENT_LE_META:
            switch(hci_event_le_meta_get_subevent_code(packet)){
                case HCI_SUBEVENT_LE_CREATE_BIG_COMPLETE:
                    if (app_state != APP_W4_BIG_CON_HANDLE) break;
                    big_con_handle = little_endian_read_16(packet, 21);
                    printf("BIG Connection Handle: %04x\n", big_con_handle);
                    app_state = APP_SET_ISO_PATH;
                    break;
                default:
                    break;
            }
        default:
            break;
    }

    const uint8_t broadcast_code[16] = { 0 };
    switch(app_state){
        case APP_CREATE_BIG:
            if (!hci_can_send_command_packet_now()) break;
            app_state = APP_W4_BIG_CON_HANDLE;
            hci_send_cmd(&hci_le_create_big, 0, adv_handle, 1, 7500, 26, 8, 2, 1, 0, 0, 0, broadcast_code);
            break;
        case APP_SET_ISO_PATH:
            if (!hci_can_send_command_packet_now()) break;
            app_state = APP_IDLE;
            hci_send_cmd(&hci_le_setup_iso_data_path, big_con_handle, 0, 0,  0, 0, 0,  0, 0, NULL);
            break;
        default:
            break;
    }
}

static void show_usage(void){
    printf("\n--- LE Audio Broadcast Source Test Console ---\n");
    printf("---\n");
    printf("Ctrl-c - exit\n");
    printf("---\n");
}

static void stdin_process(char c){
    switch (c){
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

    // parse human readable Bluetooth address
    sscanf_bd_addr(remote_addr_string, remote);

    // setup
    gap_extended_advertising_setup(&le_advertising_set, &extended_params, &adv_handle);
    gap_extended_advertising_set_adv_data(adv_handle, sizeof(extended_adv_data), extended_adv_data);
    gap_periodic_advertising_set_params(adv_handle, &periodic_params);
    gap_periodic_advertising_set_data(adv_handle, sizeof(periodic_adv_data), periodic_adv_data);
    gap_periodic_advertising_start(adv_handle, 0);
    gap_extended_advertising_start(adv_handle, 0, 0);

    // turn on!
    hci_power_control(HCI_POWER_ON);

    btstack_stdin_setup(stdin_process);
    return 0;
}
