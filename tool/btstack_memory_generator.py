#!/usr/bin/env python3
import os
import sys

import os
import sys

copyright = """/*
 * Copyright (C) 2014 BlueKitchen GmbH
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
 * FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL BLUEKITCHEN
 * GMBH OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
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
"""

hfile_header_begin = """

/*
 * btstack_memory.h
 *
 * @brief BTstack memory management using configurable memory pools
 *
 */

#ifndef BTSTACK_MEMORY_H
#define BTSTACK_MEMORY_H

#if defined __cplusplus
extern "C" {
#endif

#include "btstack_config.h"
    
// Core
#include "hci.h"
#include "l2cap.h"

// Classic
#ifdef ENABLE_CLASSIC
#include "classic/avdtp_sink.h"
#include "classic/avdtp_source.h"
#include "classic/avrcp.h"
#include "classic/bnep.h"
#include "classic/btstack_link_key_db.h"
#include "classic/btstack_link_key_db_memory.h"
#include "classic/hfp.h"
#include "classic/hid_host.h"
#include "classic/rfcomm.h"
#include "classic/sdp_server.h"
#endif

// BLE
#ifdef ENABLE_BLE
#include "ble/gatt-service/battery_service_client.h"
#include "ble/gatt-service/hids_client.h"
#include "ble/gatt-service/scan_parameters_service_client.h"
#include "ble/gatt_client.h"
#include "ble/sm.h"
#endif

#ifdef ENABLE_MESH
#include "mesh/mesh_network.h"
#include "mesh/mesh_keys.h"
#include "mesh/mesh_virtual_addresses.h"
#endif

/* API_START */

/**
 * @brief Initializes BTstack memory pools.
 */
void btstack_memory_init(void);

/**
 * @brief Deinitialize BTstack memory pools
 * @note if HAVE_MALLOC is defined, all previously allocated buffers are free'd
 */
void btstack_memory_deinit(void);

/* API_END */
"""

hfile_header_end = """
#if defined __cplusplus
}
#endif

#endif // BTSTACK_MEMORY_H
"""

cfile_header_begin = """
#define BTSTACK_FILE__ "btstack_memory.c"


/*
 *  btstack_memory.c
 *
 *  @brief BTstack memory management via configurable memory pools
 *
 *  @note code generated by tool/btstack_memory_generator.py
 *  @note returnes buffers are initialized with 0
 *
 */

#include "btstack_memory.h"
#include "btstack_memory_pool.h"
#include "btstack_debug.h"

#include <stdlib.h>

#ifdef ENABLE_MALLOC_TEST
extern "C" void * test_malloc(size_t size);
#define malloc test_malloc
#endif

#ifdef HAVE_MALLOC
typedef struct btstack_memory_buffer {
    struct btstack_memory_buffer * next;
    struct btstack_memory_buffer * prev;
} btstack_memory_buffer_t;

typedef struct {
    btstack_memory_buffer_t tracking;
    void * pointer;
} test_buffer_t;

static btstack_memory_buffer_t * btstack_memory_malloc_buffers;
static uint32_t btstack_memory_malloc_counter;

static void btstack_memory_tracking_add(btstack_memory_buffer_t * buffer){
    btstack_assert(buffer != NULL);
    if (btstack_memory_malloc_buffers != NULL) {
        // let current first item prev point to new first item
        btstack_memory_malloc_buffers->prev = buffer;
    }
    buffer->prev = NULL;
    buffer->next = btstack_memory_malloc_buffers;
    btstack_memory_malloc_buffers = buffer;

    btstack_memory_malloc_counter++;
}

static void btstack_memory_tracking_remove(btstack_memory_buffer_t * buffer){
    btstack_assert(buffer != NULL);
    if (buffer->prev == NULL){
        // first item
        btstack_memory_malloc_buffers = buffer->next;
    } else {
        buffer->prev->next = buffer->next;
    }
    if (buffer->next != NULL){
        buffer->next->prev = buffer->prev;
    }

    btstack_memory_malloc_counter--;
}
#endif

void btstack_memory_deinit(void){
#ifdef HAVE_MALLOC
    while (btstack_memory_malloc_buffers != NULL){
        btstack_memory_buffer_t * buffer = btstack_memory_malloc_buffers;
        btstack_memory_malloc_buffers = buffer->next;
        free(buffer);
        btstack_memory_malloc_counter--;
    }
    btstack_assert(btstack_memory_malloc_counter == 0);
#endif
}
"""

header_template = """STRUCT_NAME_t * btstack_memory_STRUCT_NAME_get(void);
void   btstack_memory_STRUCT_NAME_free(STRUCT_NAME_t *STRUCT_NAME);"""

code_template = """
// MARK: STRUCT_TYPE
#if !defined(HAVE_MALLOC) && !defined(POOL_COUNT)
    #if defined(POOL_COUNT_OLD_NO)
        #error "Deprecated POOL_COUNT_OLD_NO defined instead of POOL_COUNT. Please update your btstack_config.h to use POOL_COUNT."
    #else
        #define POOL_COUNT 0
    #endif
#endif

#ifdef POOL_COUNT
#if POOL_COUNT > 0
static STRUCT_TYPE STRUCT_NAME_storage[POOL_COUNT];
static btstack_memory_pool_t STRUCT_NAME_pool;
STRUCT_NAME_t * btstack_memory_STRUCT_NAME_get(void){
    void * buffer = btstack_memory_pool_get(&STRUCT_NAME_pool);
    if (buffer){
        memset(buffer, 0, sizeof(STRUCT_TYPE));
    }
    return (STRUCT_NAME_t *) buffer;
}
void btstack_memory_STRUCT_NAME_free(STRUCT_NAME_t *STRUCT_NAME){
    btstack_memory_pool_free(&STRUCT_NAME_pool, STRUCT_NAME);
}
#else
STRUCT_NAME_t * btstack_memory_STRUCT_NAME_get(void){
    return NULL;
}
void btstack_memory_STRUCT_NAME_free(STRUCT_NAME_t *STRUCT_NAME){
    UNUSED(STRUCT_NAME);
};
#endif
#elif defined(HAVE_MALLOC)

typedef struct {
    btstack_memory_buffer_t tracking;
    STRUCT_NAME_t data;
} btstack_memory_STRUCT_NAME_t;

STRUCT_NAME_t * btstack_memory_STRUCT_NAME_get(void){
    btstack_memory_STRUCT_NAME_t * buffer = (btstack_memory_STRUCT_NAME_t *) malloc(sizeof(btstack_memory_STRUCT_NAME_t));
    if (buffer){
        memset(buffer, 0, sizeof(btstack_memory_STRUCT_NAME_t));
        btstack_memory_tracking_add(&buffer->tracking);
        return &buffer->data;
    } else {
        return NULL;
    }
}
void btstack_memory_STRUCT_NAME_free(STRUCT_NAME_t *STRUCT_NAME){
    // reconstruct buffer start
    btstack_memory_buffer_t * buffer = &((btstack_memory_buffer_t *) STRUCT_NAME)[-1];
    btstack_memory_tracking_remove(buffer);
    free(buffer);
}
#endif
"""
init_header = '''
// init
void btstack_memory_init(void){
#ifdef HAVE_MALLOC
    // assert that there is no unexpected padding for combined buffer
    btstack_assert(sizeof(test_buffer_t) == sizeof(btstack_memory_buffer_t) + sizeof(void *));
#endif
  
'''

init_template = """#if POOL_COUNT > 0
    btstack_memory_pool_create(&STRUCT_NAME_pool, STRUCT_NAME_storage, POOL_COUNT, sizeof(STRUCT_TYPE));
#endif"""

def writeln(f, data):
    f.write(data + "\n")

def replacePlaceholder(template, struct_name):
    struct_type = struct_name + '_t'
    if struct_name.endswith('try'):
        pool_count = "MAX_NR_" + struct_name.upper()[:-3] + "TRIES"
    else:
        pool_count = "MAX_NR_" + struct_name.upper() + "S"
    pool_count_old_no = pool_count.replace("MAX_NR_", "MAX_NO_")
    snippet = template.replace("STRUCT_TYPE", struct_type).replace("STRUCT_NAME", struct_name).replace("POOL_COUNT_OLD_NO", pool_count_old_no).replace("POOL_COUNT", pool_count)
    return snippet
    
list_of_structs = [
    ["hci_connection"],
    ["l2cap_service", "l2cap_channel"],
]
list_of_classic_structs = [
    ["rfcomm_multiplexer", "rfcomm_service", "rfcomm_channel"],
    ["btstack_link_key_db_memory_entry"],
    ["bnep_service", "bnep_channel"],
    ["hfp_connection"],
    ["hid_host_connection"],
    ["service_record_item"],
    ["avdtp_stream_endpoint"],
    ["avdtp_connection"],
    ["avrcp_connection"],
    ["avrcp_browsing_connection"],   
]
list_of_le_structs = [
    ["battery_service_client", "gatt_client", "hids_client", "scan_parameters_service_client", "sm_lookup_entry", "whitelist_entry", "periodic_advertiser_list_entry"],
]
list_of_mesh_structs = [
    ['mesh_network_pdu', 'mesh_segmented_pdu', 'mesh_upper_transport_pdu', 'mesh_network_key', 'mesh_transport_key', 'mesh_virtual_address', 'mesh_subnet']
]

btstack_root = os.path.abspath(os.path.dirname(sys.argv[0]) + '/..')
file_name = btstack_root + "/src/btstack_memory"
print ('Generating %s.[h|c]' % file_name)

f = open(file_name+".h", "w")
writeln(f, copyright)
writeln(f, hfile_header_begin)
for struct_names in list_of_structs:
    writeln(f, "// "+ ", ".join(struct_names))
    for struct_name in struct_names:
        writeln(f, replacePlaceholder(header_template, struct_name))
    writeln(f, "")
writeln(f, "#ifdef ENABLE_CLASSIC")
for struct_names in list_of_classic_structs:
    writeln(f, "// "+ ", ".join(struct_names))
    for struct_name in struct_names:
        writeln(f, replacePlaceholder(header_template, struct_name))
    writeln(f, "")
writeln(f, "#endif")
writeln(f, "#ifdef ENABLE_BLE")
for struct_names in list_of_le_structs:
    writeln(f, "// "+ ", ".join(struct_names))
    for struct_name in struct_names:
        writeln(f, replacePlaceholder(header_template, struct_name))
writeln(f, "#endif")
writeln(f, "#ifdef ENABLE_MESH")
for struct_names in list_of_mesh_structs:
    writeln(f, "// "+ ", ".join(struct_names))
    for struct_name in struct_names:
        writeln(f, replacePlaceholder(header_template, struct_name))
writeln(f, "#endif")
writeln(f, hfile_header_end)
f.close();


f = open(file_name+".c", "w")
writeln(f, copyright)
writeln(f, cfile_header_begin)
for struct_names in list_of_structs:
    for struct_name in struct_names:
        writeln(f, replacePlaceholder(code_template, struct_name))
    writeln(f, "")
writeln(f, "#ifdef ENABLE_CLASSIC")
for struct_names in list_of_classic_structs:
    for struct_name in struct_names:
        writeln(f, replacePlaceholder(code_template, struct_name))
    writeln(f, "")
writeln(f, "#endif")
writeln(f, "#ifdef ENABLE_BLE")
for struct_names in list_of_le_structs:
    for struct_name in struct_names:
        writeln(f, replacePlaceholder(code_template, struct_name))
    writeln(f, "")
writeln(f, "#endif")
writeln(f, "#ifdef ENABLE_MESH")
for struct_names in list_of_mesh_structs:
    for struct_name in struct_names:
        writeln(f, replacePlaceholder(code_template, struct_name))
    writeln(f, "")
writeln(f, "#endif")

f.write(init_header)
for struct_names in list_of_structs:
    for struct_name in struct_names:
        writeln(f, replacePlaceholder(init_template, struct_name))
writeln(f, "#ifdef ENABLE_CLASSIC")
for struct_names in list_of_classic_structs:
    for struct_name in struct_names:
        writeln(f, replacePlaceholder(init_template, struct_name))
writeln(f, "#endif")
writeln(f, "#ifdef ENABLE_BLE")
for struct_names in list_of_le_structs:
    for struct_name in struct_names:
        writeln(f, replacePlaceholder(init_template, struct_name))
writeln(f, "#endif")
writeln(f, "#ifdef ENABLE_MESH")
for struct_names in list_of_mesh_structs:
    for struct_name in struct_names:
        writeln(f, replacePlaceholder(init_template, struct_name))
writeln(f, "#endif")
writeln(f, "}")
f.close();
    
# also generate test code
test_header = """
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// malloc hook
static int simulate_no_memory;
extern "C" void * test_malloc(size_t size);
void * test_malloc(size_t size){
    if (simulate_no_memory) return NULL;
    return malloc(size);
}

#include "btstack_config.h"

#include "CppUTest/TestHarness.h"
#include "CppUTest/CommandLineTestRunner.h"

#include "bluetooth_data_types.h"
#include "btstack_util.h"
#include "btstack_memory.h"


TEST_GROUP(btstack_memory){
    void setup(void){
        btstack_memory_init();
        simulate_no_memory = 0;
    }
};

#ifdef HAVE_MALLOC
TEST(btstack_memory, deinit){
    // alloc buffers 1,2,3
    hci_connection_t * buffer_1 = btstack_memory_hci_connection_get();
    hci_connection_t * buffer_2 = btstack_memory_hci_connection_get();
    hci_connection_t * buffer_3 = btstack_memory_hci_connection_get();
    // free first one in list
    btstack_memory_hci_connection_free(buffer_3);
    // free second one in list
    btstack_memory_hci_connection_free(buffer_1);
    // leave buffer in list
    (void) buffer_2;
    btstack_memory_deinit();
}
#endif

"""

test_template = """

TEST(btstack_memory, STRUCT_NAME_GetAndFree){
    STRUCT_NAME_t * context;
#ifdef HAVE_MALLOC
    context = btstack_memory_STRUCT_NAME_get();
    CHECK(context != NULL);
    btstack_memory_STRUCT_NAME_free(context);
#else
#ifdef POOL_COUNT
    // single
    context = btstack_memory_STRUCT_NAME_get();
    CHECK(context != NULL);
    btstack_memory_STRUCT_NAME_free(context);
#else
    // none
    context = btstack_memory_STRUCT_NAME_get();
    CHECK(context == NULL);
    btstack_memory_STRUCT_NAME_free(context);
#endif
#endif
}

TEST(btstack_memory, STRUCT_NAME_NotEnoughBuffers){
    STRUCT_NAME_t * context;
#ifdef HAVE_MALLOC
    simulate_no_memory = 1;
#else
#ifdef POOL_COUNT
    int i;
    // alloc all static buffers
    for (i = 0; i < POOL_COUNT; i++){
        context = btstack_memory_STRUCT_NAME_get();
        CHECK(context != NULL);
    }
#endif
#endif
    // get one more
    context = btstack_memory_STRUCT_NAME_get();
    CHECK(context == NULL);
}
"""

test_footer = """
int main (int argc, const char * argv[]){
    return CommandLineTestRunner::RunAllTests(argc, argv);
}
"""

file_name = btstack_root + "/test/btstack_memory/btstack_memory_test.c"
print ('Generating %s' % file_name)

f = open(file_name, "w")
writeln(f, copyright)
writeln(f, test_header)
for struct_names in list_of_structs:
    for struct_name in struct_names:
        writeln(f, replacePlaceholder(test_template, struct_name))
writeln(f, "#ifdef ENABLE_CLASSIC")
for struct_names in list_of_classic_structs:
    for struct_name in struct_names:
        writeln(f, replacePlaceholder(test_template, struct_name))
writeln(f, "#endif")
writeln(f, "#ifdef ENABLE_BLE")
for struct_names in list_of_le_structs:
    for struct_name in struct_names:
        writeln(f, replacePlaceholder(test_template, struct_name))
writeln(f, "#endif")
writeln(f, "#ifdef ENABLE_MESH")
for struct_names in list_of_mesh_structs:
    for struct_name in struct_names:
        writeln(f, replacePlaceholder(test_template, struct_name))
writeln(f, "#endif")
writeln(f, test_footer)