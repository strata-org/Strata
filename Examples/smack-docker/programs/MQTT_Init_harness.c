// Imported verbatim from FreeRTOS/coreMQTT
//   test/cbmc/proofs/MQTT_Init/MQTT_Init_harness.c
// Source bundle: test/cbmc/include/core_mqtt_config.h, source/interface/transport_interface.h, source/include/core_mqtt_serializer.h, source/include/core_mqtt.h, source/include/core_mqtt_state.h, source/include/core_mqtt_config_defaults.h, source/include/private/core_mqtt_serializer_private.h, source/core_mqtt_serializer.c, source/core_mqtt_state.c, source/core_mqtt.c
// Adapter prelude shims CBMC primitives onto SMACK's __VERIFIER_*.

#include "smack.h"
#include <stdint.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stddef.h>
#include <limits.h>
#include <string.h>
#include <assert.h>

// CBMC primitive shims
#define __CPROVER_assume(x)           __VERIFIER_assume(x)
#define __CPROVER_havoc_object(p)     ((void)(p))
#define __CPROVER_r_ok(p, n)          ((void)(p), (void)(n), 1)
#define __CPROVER_w_ok(p, n)          ((void)(p), (void)(n), 1)

// CBMC built-in constants (reasonable bounds for SMACK)
#ifndef CBMC_MAX_OBJECT_SIZE
#  define CBMC_MAX_OBJECT_SIZE (SIZE_MAX >> 1)
#endif
#ifndef CBMC_MAX_MALLOC_SIZE
#  define CBMC_MAX_MALLOC_SIZE (SIZE_MAX >> 1)
#endif

// Logging macros used by FreeRTOS libs (no-ops for verification)
#ifndef LogError
#  define LogError(x)
#endif
#ifndef LogWarn
#  define LogWarn(x)
#endif
#ifndef LogInfo
#  define LogInfo(x)
#endif
#ifndef LogDebug
#  define LogDebug(x)
#endif
#define assert(expr) __VERIFIER_assume(expr)

// === test/cbmc/include/core_mqtt_config.h (verbatim from upstream) ===
/*
 * coreMQTT
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

/**
 * @file core_mqtt_config.h
 * @brief This header sets configuration macros for the MQTT library.
 */
#ifndef CORE_MQTT_CONFIG_H_
#define CORE_MQTT_CONFIG_H_

/**
 * @brief Determines the maximum number of MQTT PUBLISH messages, pending
 * acknowledgement at a time, that are supported for incoming and outgoing
 * direction of messages, separately.
 *
 * QoS 1 and 2 MQTT PUBLISHes require acknowledgement from the server before
 * they can be completed. While they are awaiting the acknowledgement, the
 * client must maintain information about their state. The value of this
 * macro sets the limit on how many simultaneous PUBLISH states an MQTT
 * context maintains, separately, for both incoming and outgoing direction of
 * PUBLISHes.
 *
 * @note This definition must exist in order to compile. 10U is a typical value
 * used in the MQTT demos.
 */
#define MQTT_STATE_ARRAY_MAX_COUNT              ( 10U )

/**
 * @brief Retry count for reading CONNACK from network.
 *
 * The MQTT_MAX_CONNACK_RECEIVE_RETRY_COUNT will be used only when the
 * timeoutMs parameter of #MQTT_Connect() is passed as 0 . The transport
 * receive for CONNACK will be retried MQTT_MAX_CONNACK_RECEIVE_RETRY_COUNT
 * times before timing out. A value of 0 for this config will cause the
 * transport receive for CONNACK  to be invoked only once.
 */
#define MQTT_MAX_CONNACK_RECEIVE_RETRY_COUNT    ( 2U )

/**
 * @brief Number of milliseconds to wait for a ping response to a ping
 * request as part of the keep-alive mechanism.
 *
 * If a ping response is not received before this timeout, then
 * #MQTT_ProcessLoop will return #MQTTKeepAliveTimeout.
 */
#define MQTT_PINGRESP_TIMEOUT_MS                ( 5000U )

/**
 * @brief The maximum duration of receiving no data over network when
 * attempting to read an incoming MQTT packet by the #MQTT_ProcessLoop or
 * #MQTT_ReceiveLoop API functions.
 *
 * When an incoming MQTT packet is detected, the transport receive function
 * may be called multiple times until all the expected number of bytes for the
 * packet are received. This timeout represents the maximum duration of polling
 * for any data to be received over the network for the incoming.
 * If the timeout expires, the #MQTT_ProcessLoop or #MQTT_ReceiveLoop functions
 * return #MQTTRecvFailed.
 *
 * This is set to 1 to exit right away after a zero is received in the transport
 * receive stub. There is no added value, in proving memory safety, to repeat
 * the logic that checks if the polling timeout is reached.
 */
#define MQTT_RECV_POLLING_TIMEOUT_MS            ( 1U )

#endif /* ifndef CORE_MQTT_CONFIG_H_ */

// === source/interface/transport_interface.h (verbatim from upstream) ===
/*
 * coreMQTT
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

/**
 * @file transport_interface.h
 * @brief Transport interface definitions to send and receive data over the
 * network.
 */
#ifndef TRANSPORT_INTERFACE_H_
#define TRANSPORT_INTERFACE_H_

#include <stdint.h>
#include <stddef.h>

/* *INDENT-OFF* */
#ifdef __cplusplus
    extern "C" {
#endif
/* *INDENT-ON* */

/**
 * @transportpage
 * @brief The transport interface definition.
 *
 * @transportsectionoverview
 *
 * The transport interface is a set of APIs that must be implemented using an
 * external transport layer protocol. The transport interface is defined in
 * @ref transport_interface.h. This interface allows protocols like MQTT and
 * HTTP to send and receive data over the transport layer. This
 * interface does not handle connection and disconnection to the server of
 * interest. The connection, disconnection, and other transport settings, like
 * timeout and TLS setup, must be handled in the user application.
 * <br>
 *
 * The functions that must be implemented are:<br>
 * - [Transport Receive](@ref TransportRecv_t)
 * - [Transport Send](@ref TransportSend_t)
 *
 * Each of the functions above take in an opaque context @ref NetworkContext_t.
 * The functions above and the context are also grouped together in the
 * @ref TransportInterface_t structure:<br><br>
 * @snippet this define_transportinterface
 * <br>
 *
 * @transportsectionimplementation
 *
 * The following steps give guidance on implementing the transport interface:
 *
 * -# Implementing @ref NetworkContext_t<br><br>
 * @snippet this define_networkcontext
 * <br>
 * @ref NetworkContext_t is the incomplete type <b>struct NetworkContext</b>.
 * The implemented struct NetworkContext must contain all of the information
 * that is needed to receive and send data with the @ref TransportRecv_t
 * and the @ref TransportSend_t implementations.<br>
 * In the case of TLS over TCP, struct NetworkContext is typically implemented
 * with the TCP socket context and a TLS context.<br><br>
 * <b>Example code:</b>
 * @code{c}
 * struct NetworkContext
 * {
 *     struct MyTCPSocketContext tcpSocketContext;
 *     struct MyTLSContext tlsContext;
 * };
 * @endcode
 * <br>
 * -# Implementing @ref TransportRecv_t<br><br>
 * @snippet this define_transportrecv
 * <br>
 * This function is expected to populate a buffer, with bytes received from the
 * transport, and return the number of bytes placed in the buffer.
 * In the case of TLS over TCP, @ref TransportRecv_t is typically implemented by
 * calling the TLS layer function to receive data. In case of plaintext TCP
 * without TLS, it is typically implemented by calling the TCP layer receive
 * function. @ref TransportRecv_t may be invoked multiple times by the protocol
 * library, if fewer bytes than were requested to receive are returned.
 * Please note that it is HIGHLY RECOMMENDED that the transport receive implementation does NOT block.
 * <br><br>
 * <b>Example code:</b>
 * @code{c}
 * int32_t myNetworkRecvImplementation( NetworkContext_t * pNetworkContext,
 *                                      void * pBuffer,
 *                                      size_t bytesToRecv )
 * {
 *     int32_t bytesReceived = 0;
 *     bool callTlsRecvFunc = true;
 *
 *     // For a single byte read request, check if data is available on the network.
 *     if( bytesToRecv == 1 )
 *     {
 *        // If no data is available on the network, do not call TLSRecv
 *        // to avoid blocking for socket timeout.
 *        if( TLSRecvCount( pNetworkContext->tlsContext ) == 0 )
 *        {
 *            callTlsRecvFunc = false;
 *        }
 *     }
 *
 *     if( callTlsRecvFunc == true )
 *     {
 *        bytesReceived = TLSRecv( pNetworkContext->tlsContext,
 *                                 pBuffer,
 *                                 bytesToRecv,
 *                                 MY_SOCKET_TIMEOUT );
 *        if( bytesReceived < 0 )
 *        {
 *           // If the error code represents a timeout, then the return
 *           // code should be translated to zero so that the caller
 *           // can retry the read operation.
 *           if( bytesReceived == MY_SOCKET_ERROR_TIMEOUT )
 *           {
 *              bytesReceived = 0;
 *           }
 *        }
 *        // Handle other cases.
 *     }
 *     return bytesReceived;
 * }
 * @endcode
 * <br>
 * -# Implementing @ref TransportSend_t<br><br>
 * @snippet this define_transportsend
 * <br>
 * This function is expected to send the bytes, in the given buffer over the
 * transport, and return the number of bytes sent.
 * In the case of TLS over TCP, @ref TransportSend_t is typically implemented by
 * calling the TLS layer function to send data. In case of plaintext TCP
 * without TLS, it is typically implemented by calling the TCP layer send
 * function. @ref TransportSend_t may be invoked multiple times by the protocol
 * library, if fewer bytes than were requested to send are returned.
 * <br><br>
 * <b>Example code:</b>
 * @code{c}
 * int32_t myNetworkSendImplementation( NetworkContext_t * pNetworkContext,
 *                                      const void * pBuffer,
 *                                      size_t bytesToSend )
 * {
 *     int32_t bytesSent = 0;
 *     bytesSent = TLSSend( pNetworkContext->tlsContext,
 *                          pBuffer,
 *                          bytesToSend,
 *                          MY_SOCKET_TIMEOUT );
 *
 *      // If underlying TCP buffer is full, set the return value to zero
 *      // so that caller can retry the send operation.
 *     if( bytesSent == MY_SOCKET_ERROR_BUFFER_FULL )
 *     {
 *          bytesSent = 0;
 *     }
 *     else if( bytesSent < 0 )
 *     {
 *         // Handle socket error.
 *     }
 *     // Handle other cases.
 *
 *     return bytesSent;
 * }
 * @endcode
 */

/**
 * @transportstruct
 * @typedef NetworkContext_t
 * @brief The NetworkContext is an incomplete type. An implementation of this
 * interface must define struct NetworkContext for the system requirements.
 * This context is passed into the network interface functions.
 */
/* @[define_networkcontext] */
struct NetworkContext;
typedef struct NetworkContext NetworkContext_t;
/* @[define_networkcontext] */

/**
 * @transportcallback
 * @brief Transport interface for receiving data on the network.
 *
 * @note It is HIGHLY RECOMMENDED that the transport receive
 * implementation does NOT block.
 * coreMQTT will continue to call the transport interface if it receives
 * a partial packet until it accumulates enough data to get the complete
 * MQTT packet.
 * A non‐blocking implementation is also essential so that the library's inbuilt
 * keep‐alive mechanism can work properly, given the user chooses to use
 * that over their own keep alive mechanism.
 *
 * @param[in] pNetworkContext Implementation-defined network context.
 * @param[in] pBuffer Buffer to receive the data into.
 * @param[in] bytesToRecv Number of bytes requested from the network.
 *
 * @return The number of bytes received or a negative value to indicate
 * error.
 *
 * @note If no data is available on the network to read and no error
 * has occurred, zero MUST be the return value. A zero return value
 * SHOULD represent that the read operation can be retried by calling
 * the API function. Zero MUST NOT be returned if a network disconnection
 * has occurred.
 */
/* @[define_transportrecv] */
typedef int32_t ( * TransportRecv_t )( NetworkContext_t * pNetworkContext,
                                       void * pBuffer,
                                       size_t bytesToRecv );
/* @[define_transportrecv] */

/**
 * @transportcallback
 * @brief Transport interface for sending data over the network.
 *
 * @param[in] pNetworkContext Implementation-defined network context.
 * @param[in] pBuffer Buffer containing the bytes to send over the network stack.
 * @param[in] bytesToSend Number of bytes to send over the network.
 *
 * @return The number of bytes sent or a negative value to indicate error.
 *
 * @note If no data is transmitted over the network due to a full TX buffer and
 * no network error has occurred, this MUST return zero as the return value.
 * A zero return value SHOULD represent that the send operation can be retried
 * by calling the API function. Zero MUST NOT be returned if a network disconnection
 * has occurred.
 */
/* @[define_transportsend] */
typedef int32_t ( * TransportSend_t )( NetworkContext_t * pNetworkContext,
                                       const void * pBuffer,
                                       size_t bytesToSend );
/* @[define_transportsend] */

/**
 * @brief Transport vector structure for sending multiple messages.
 */
typedef struct TransportOutVector
{
    /**
     * @brief Base address of data.
     */
    const void * iov_base;

    /**
     * @brief Length of data in buffer.
     */
    size_t iov_len;
} TransportOutVector_t;

/**
 * @transportcallback
 * @brief Transport interface function for "vectored" / scatter-gather based
 * writes. This function is expected to iterate over the list of vectors pIoVec
 * having ioVecCount entries containing portions of one MQTT message at a maximum.
 * If the proper functionality is available, then the data in the list should be
 * copied to the underlying TCP buffer before flushing the buffer. Implementing it
 * in this fashion  will lead to sending of fewer TCP packets for all the values
 * in the list.
 *
 * @note If the proper write functionality is not present for a given device/IP-stack,
 * then there is no strict requirement to implement write. Only the send and recv
 * interfaces must be defined for the application to work properly.
 *
 * @param[in] pNetworkContext Implementation-defined network context.
 * @param[in] pIoVec An array of TransportIoVector_t structs.
 * @param[in] ioVecCount Number of TransportIoVector_t in pIoVec.
 *
 * @return The number of bytes written or a negative value to indicate error.
 *
 * @note If no data is written to the buffer due to the buffer being full this MUST
 * return zero as the return value.
 * A zero return value SHOULD represent that the write operation can be retried
 * by calling the API function. Zero MUST NOT be returned if a network disconnection
 * has occurred.
 */
/* @[define_transportwritev] */
typedef int32_t ( * TransportWritev_t )( NetworkContext_t * pNetworkContext,
                                         TransportOutVector_t * pIoVec,
                                         size_t ioVecCount );
/* @[define_transportwritev] */

/**
 * @transportstruct
 * @brief The transport layer interface.
 */
/* @[define_transportinterface] */
typedef struct TransportInterface
{
    TransportRecv_t recv;               /**< Transport receive function pointer. */
    TransportSend_t send;               /**< Transport send function pointer. */
    TransportWritev_t writev;           /**< Transport writev function pointer. */
    NetworkContext_t * pNetworkContext; /**< Implementation-defined network context. */
} TransportInterface_t;
/* @[define_transportinterface] */

/* *INDENT-OFF* */
#ifdef __cplusplus
    }
#endif
/* *INDENT-ON* */

#endif /* ifndef TRANSPORT_INTERFACE_H_ */

// === source/include/core_mqtt_serializer.h (verbatim from upstream) ===
/*
 * coreMQTT
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

/**
 * @file core_mqtt_serializer.h
 * @brief User-facing functions for serializing and deserializing MQTT 5.0
 * packets. This header should be included for building a lighter weight MQTT
 * client than the managed CSDK MQTT library API in core_mqtt.h, by using the
 * serializer and de-serializer functions exposed in this file's API.
 */
#ifndef CORE_MQTT_SERIALIZER_H
#define CORE_MQTT_SERIALIZER_H

#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

/* *INDENT-OFF* */
#ifdef __cplusplus
    extern "C" {
#endif
/* *INDENT-ON */

/* MQTT packet types. */

/**
 * @addtogroup mqtt_constants
 * @{
 */
#define MQTT_PACKET_TYPE_CONNECT        ( ( uint8_t ) 0x10U )  /**< @brief CONNECT (client-to-server). */
#define MQTT_PACKET_TYPE_CONNACK        ( ( uint8_t ) 0x20U )  /**< @brief CONNACK (server-to-client). */
#define MQTT_PACKET_TYPE_PUBLISH        ( ( uint8_t ) 0x30U )  /**< @brief PUBLISH (bidirectional). */
#define MQTT_PACKET_TYPE_PUBACK         ( ( uint8_t ) 0x40U )  /**< @brief PUBACK (bidirectional). */
#define MQTT_PACKET_TYPE_PUBREC         ( ( uint8_t ) 0x50U )  /**< @brief PUBREC (bidirectional). */
#define MQTT_PACKET_TYPE_PUBREL         ( ( uint8_t ) 0x62U )  /**< @brief PUBREL (bidirectional). */
#define MQTT_PACKET_TYPE_PUBCOMP        ( ( uint8_t ) 0x70U )  /**< @brief PUBCOMP (bidirectional). */
#define MQTT_PACKET_TYPE_SUBSCRIBE      ( ( uint8_t ) 0x82U )  /**< @brief SUBSCRIBE (client-to-server). */
#define MQTT_PACKET_TYPE_SUBACK         ( ( uint8_t ) 0x90U )  /**< @brief SUBACK (server-to-client). */
#define MQTT_PACKET_TYPE_UNSUBSCRIBE    ( ( uint8_t ) 0xA2U )  /**< @brief UNSUBSCRIBE (client-to-server). */
#define MQTT_PACKET_TYPE_UNSUBACK       ( ( uint8_t ) 0xB0U )  /**< @brief UNSUBACK (server-to-client). */
#define MQTT_PACKET_TYPE_PINGREQ        ( ( uint8_t ) 0xC0U )  /**< @brief PINGREQ (client-to-server). */
#define MQTT_PACKET_TYPE_PINGRESP       ( ( uint8_t ) 0xD0U )  /**< @brief PINGRESP (server-to-client). */
#define MQTT_PACKET_TYPE_DISCONNECT     ( ( uint8_t ) 0xE0U )  /**< @brief DISCONNECT (client-to-server). */
#define MQTT_PACKET_TYPE_AUTH           ( ( uint8_t ) 0xF0U )  /**< @brief AUTH (bidirectional). */
/** @} */

/**
 * @addtogroup mqtt_constants
 * @{
 */

/**
 * @brief Convenience pointers for the @c pOptionalMqttPacketType parameter
 * of the @c MQTTPropAdd_* functions.
 *
 * Pass one of these to enable runtime validation that a property is allowed
 * in the intended packet type. Pass @ref MQTT_PROP_NO_VALIDATE (NULL) to
 * skip validation.
 *
 * @code{c}
 * MQTTPropAdd_SessionExpiry( &props, 3600, MQTT_PROP_VALIDATE_CONNECT );
 * MQTTPropAdd_PayloadFormat( &props, 1,    MQTT_PROP_VALIDATE_PUBLISH );
 * MQTTPropAdd_UserProp( &props, &up,       MQTT_PROP_NO_VALIDATE );
 * @endcode
 */
/*
 * The five file-scope constants below are intentionally named in the same
 * MQTT_PACKET_TYPE_* family as the existing MQTT_PACKET_TYPE_* macros a few
 * lines above, and their values match those macros. Coverity flags this as
 * MISRA C:2012 Rule 2.2 (unused redundant expression — the name reuse looks
 * redundant to the analyser) and Rule 2.8 (unused objects at file scope).
 * Both deviations are accepted because these constants have to be addressable
 * storage — the MQTT_PROP_VALIDATE_* macros below take their addresses so
 * that callers can pass a typed `const uint8_t *` argument to the
 * MQTTPropAdd_* APIs without resorting to C99 compound literals. Macros
 * cannot be addressed, which is why we cannot reuse the existing
 * MQTT_PACKET_TYPE_* macros directly here.
 *
 * See MISRA.md in the repository root for the project-wide deviation record.
 */
/* More details at: https://github.com/FreeRTOS/coreMQTT/blob/main/MISRA.md#rule-22 */
/* More details at: https://github.com/FreeRTOS/coreMQTT/blob/main/MISRA.md#rule-28 */
/* coverity[misra_c_2012_rule_2_2_violation] */
/* coverity[misra_c_2012_rule_2_8_violation] */
static const uint8_t MQTT_PACKET_TYPE_CONNECT_VAL     = ( uint8_t ) 0x10U;  /**< @brief CONNECT value for property validation. */
/* More details at: https://github.com/FreeRTOS/coreMQTT/blob/main/MISRA.md#rule-22 */
/* More details at: https://github.com/FreeRTOS/coreMQTT/blob/main/MISRA.md#rule-28 */
/* coverity[misra_c_2012_rule_2_2_violation] */
/* coverity[misra_c_2012_rule_2_8_violation] */
static const uint8_t MQTT_PACKET_TYPE_PUBLISH_VAL     = ( uint8_t ) 0x30U;  /**< @brief PUBLISH value for property validation. */
/* More details at: https://github.com/FreeRTOS/coreMQTT/blob/main/MISRA.md#rule-22 */
/* More details at: https://github.com/FreeRTOS/coreMQTT/blob/main/MISRA.md#rule-28 */
/* coverity[misra_c_2012_rule_2_2_violation] */
/* coverity[misra_c_2012_rule_2_8_violation] */
static const uint8_t MQTT_PACKET_TYPE_SUBSCRIBE_VAL   = ( uint8_t ) 0x82U;  /**< @brief SUBSCRIBE value for property validation. */
/* More details at: https://github.com/FreeRTOS/coreMQTT/blob/main/MISRA.md#rule-22 */
/* More details at: https://github.com/FreeRTOS/coreMQTT/blob/main/MISRA.md#rule-28 */
/* coverity[misra_c_2012_rule_2_2_violation] */
/* coverity[misra_c_2012_rule_2_8_violation] */
static const uint8_t MQTT_PACKET_TYPE_UNSUBSCRIBE_VAL = ( uint8_t ) 0xA2U;  /**< @brief UNSUBSCRIBE value for property validation. */
/* More details at: https://github.com/FreeRTOS/coreMQTT/blob/main/MISRA.md#rule-22 */
/* More details at: https://github.com/FreeRTOS/coreMQTT/blob/main/MISRA.md#rule-28 */
/* coverity[misra_c_2012_rule_2_2_violation] */
/* coverity[misra_c_2012_rule_2_8_violation] */
static const uint8_t MQTT_PACKET_TYPE_DISCONNECT_VAL  = ( uint8_t ) 0xE0U;  /**< @brief DISCONNECT value for property validation. */

#define MQTT_PROP_VALIDATE_CONNECT      ( &MQTT_PACKET_TYPE_CONNECT_VAL )      /**< @brief Validate property for CONNECT. */
#define MQTT_PROP_VALIDATE_PUBLISH      ( &MQTT_PACKET_TYPE_PUBLISH_VAL )      /**< @brief Validate property for PUBLISH. */
#define MQTT_PROP_VALIDATE_SUBSCRIBE    ( &MQTT_PACKET_TYPE_SUBSCRIBE_VAL )    /**< @brief Validate property for SUBSCRIBE. */
#define MQTT_PROP_VALIDATE_UNSUBSCRIBE  ( &MQTT_PACKET_TYPE_UNSUBSCRIBE_VAL )  /**< @brief Validate property for UNSUBSCRIBE. */
#define MQTT_PROP_VALIDATE_DISCONNECT   ( &MQTT_PACKET_TYPE_DISCONNECT_VAL )   /**< @brief Validate property for DISCONNECT. */
#define MQTT_PROP_NO_VALIDATE           ( NULL )                               /**< @brief Skip packet type validation. */

/** @} */

/**
 * @ingroup mqtt_constants
 * @brief The size of MQTT PUBACK, PUBREC, PUBREL, and PUBCOMP packets, per MQTT spec.
 */
#define MQTT_PUBLISH_ACK_PACKET_SIZE    ( 4UL )

#define MQTT_SUBSCRIBE_QOS1                    ( 0U ) /**< @brief MQTT SUBSCRIBE QoS1 flag. */
#define MQTT_SUBSCRIBE_QOS2                    ( 1U ) /**< @brief MQTT SUBSCRIBE QoS2 flag. */
#define MQTT_SUBSCRIBE_NO_LOCAL                ( 2U ) /**< @brief MQTT SUBSCRIBE no local flag. */
#define MQTT_SUBSCRIBE_RETAIN_AS_PUBLISHED     ( 3U ) /**< @brief MQTT SUBSCRIBE retain as published flag. */
#define MQTT_SUBSCRIBE_RETAIN_HANDLING1        ( 4U ) /**<@brief MQTT SUBSCRIBE Retain Handling Option 1 */
#define MQTT_SUBSCRIBE_RETAIN_HANDLING2        ( 5U ) /**<@brief Retain Handling Option 2   -> in core_mqtt_serializer.c */

/* CONNECT PROPERTIES. */

/**
* @brief Session expiry id.
*/
#define MQTT_SESSION_EXPIRY_ID      ( 0x11U )

/**
* @brief Receive maximum id.
*/
#define MQTT_RECEIVE_MAX_ID         ( 0x21U )

/**
* @brief Maximum packet size  id.
*/
#define MQTT_MAX_PACKET_SIZE_ID     ( 0x27U )

/**
* @brief Topic alias size id.
*/
#define MQTT_TOPIC_ALIAS_MAX_ID     ( 0x22U )

/**
* @brief Request response id.
*/
#define MQTT_REQUEST_RESPONSE_ID    ( 0x19U )

/**
* @brief Request problem id.
*/
#define MQTT_REQUEST_PROBLEM_ID     ( 0x17U )

/**
* @brief User property id.
*/
#define MQTT_USER_PROPERTY_ID       ( 0x26U )

/**
* @brief Authentication method id.
*/
#define MQTT_AUTH_METHOD_ID         ( 0x15U )

/**
* @brief  Authentication data id.
*/
#define MQTT_AUTH_DATA_ID           ( 0x16U )


/* Publish properties. */

/**
* @brief Will delay id.
*/
#define MQTT_WILL_DELAY_ID          ( 0x18U )

/**
* @brief Payload format id.
*/
#define MQTT_PAYLOAD_FORMAT_ID      ( 0x01U )

/**
* @brief Message Expiry id.
*/
#define MQTT_MSG_EXPIRY_ID          ( 0x02U )

/**
* @brief Content type id.
*/
#define MQTT_CONTENT_TYPE_ID        ( 0x03U )

/**
* @brief Response topic id.
*/
#define MQTT_RESPONSE_TOPIC_ID      ( 0x08U )

/**
* @brief Correlation data id.
*/
#define MQTT_CORRELATION_DATA_ID    ( 0x09U )

/**
* @brief Topic alias id.
*/
#define MQTT_TOPIC_ALIAS_ID         ( 0x23U )


/* CONNACK PROPERTIES. */

/**
* @brief Max qos id.
*/
#define MQTT_MAX_QOS_ID              ( 0x24U )

/**
* @brief Retain available id.
*/
#define MQTT_RETAIN_AVAILABLE_ID     ( 0x25U )

/**
* @brief Assigned client identifier id.
*/
#define MQTT_ASSIGNED_CLIENT_ID      ( 0x12U )

/**
* @brief Reason string id.
*/
#define MQTT_REASON_STRING_ID        ( 0x1FU )

/**
* @brief Wildcard available id.
*/
#define MQTT_WILDCARD_ID             ( 0x28U )

/**
* @brief Subscription available id.
*/
#define MQTT_SUB_AVAILABLE_ID        ( 0x29U )

/**
* @brief Shared subscription id.
*/
#define MQTT_SHARED_SUB_ID           ( 0x2AU )

/**
* @brief Server keep alive id.
*/
#define MQTT_SERVER_KEEP_ALIVE_ID    ( 0x13U )

/**
* @brief Response information id.
*/

#define MQTT_RESPONSE_INFO_ID    ( 0x1AU )

/**
* @brief Server reference  id.
*/
#define MQTT_SERVER_REF_ID       ( 0x1CU )

/**
* @brief Subscription ID id
*/
#define MQTT_SUBSCRIPTION_ID_ID          ( 0x0BU )

/* Structures defined in this file. */
struct MQTTFixedBuffer;
struct MQTTConnectInfo;
struct MQTTSubscribeInfo;
struct MQTTPublishInfo;
struct MQTTPacketInfo;

/**
 * @ingroup mqtt_enum_types
 * @brief Return codes from MQTT functions.
 */
typedef enum MQTTStatus
{
    MQTTSuccess = 0,                /**< Function completed successfully. */
    MQTTBadParameter,               /**< At least one parameter was invalid. */
    MQTTNoMemory,                   /**< A provided buffer was too small. */
    MQTTSendFailed,                 /**< The transport send function failed. */
    MQTTRecvFailed,                 /**< The transport receive function failed. */
    MQTTBadResponse,                /**< An invalid packet was received from the server. It is recommended that application closes the connection.  */
    MQTTServerRefused,              /**< The server refused a CONNECT. */
    MQTTNoDataAvailable,            /**< No data available from the transport interface. */
    MQTTIllegalState,               /**< An illegal state in the state record. */
    MQTTStateCollision,             /**< A collision with an existing state record entry. */
    MQTTKeepAliveTimeout,           /**< Timeout while waiting for PINGRESP. */
    MQTTNeedMoreBytes,              /**< MQTT_ProcessLoop/MQTT_ReceiveLoop has received
                                    incomplete data; it should be called again (probably after
                                    a delay). */
    MQTTEndOfProperties,            /**< End of properties reached while parsing MQTT packet. */
    MQTTStatusConnected,            /**< MQTT connection is established with the broker. */
    MQTTStatusNotConnected,         /**< MQTT connection is not established with the broker. */
    MQTTStatusDisconnectPending,    /**< Transport Interface has failed and MQTT connection needs to be closed. */
    MQTTPublishStoreFailed,         /**< User provided API to store a copy of outgoing publish for retransmission  purposes,
                                    has failed. */
    MQTTPublishRetrieveFailed,       /**< User provided API to retrieve the copy of a publish while reconnecting
                                    with an unclean session has failed. */
    MQTTEventCallbackFailed         /**< Error in the user provided event callback function. */
} MQTTStatus_t;

/**
 * @ingroup mqtt_enum_types
 * @brief MQTT Quality of Service values.
 */
typedef enum MQTTQoS
{
    MQTTQoS0 = 0, /**< Delivery at most once. */
    MQTTQoS1 = 1, /**< Delivery at least once. */
    MQTTQoS2 = 2  /**< Delivery exactly once. */
} MQTTQoS_t;

/**
 * @ingroup mqtt_struct_types
 * @brief Buffer passed to MQTT library.
 *
 * These buffers are not copied and must remain in scope for the duration of the
 * MQTT operation.
 */
typedef struct MQTTFixedBuffer
{
    uint8_t * pBuffer; /**< @brief Pointer to buffer. */
    size_t size;       /**< @brief Size of buffer. */
} MQTTFixedBuffer_t;

/**
 * @ingroup mqtt_struct_types
 * @brief MQTT CONNECT packet parameters.
 */
typedef struct MQTTConnectInfo
{
    /**
     * @brief Whether to establish a new, clean session or resume a previous session.
     */
    bool cleanSession;

    /**
     * @brief MQTT keep alive period.
     */
    uint16_t keepAliveSeconds;

    /**
     * @brief MQTT client identifier. Must be unique per client.
     */
    const char * pClientIdentifier;

    /**
     * @brief Length of the client identifier.
     */
    size_t clientIdentifierLength;

    /**
     * @brief MQTT user name. Set to NULL if not used.
     */
    const char * pUserName;

    /**
     * @brief Length of MQTT user name. Set to 0 if not used.
     */
    size_t userNameLength;

    /**
     * @brief MQTT password. Set to NULL if not used.
     */
    const char * pPassword;

    /**
     * @brief Length of MQTT password. Set to 0 if not used.
     */
    size_t passwordLength;
} MQTTConnectInfo_t;

/**
 * @ingroup mqtt_enum_types
 * @brief Retain Handling types.
 */
typedef enum MQTTRetainHandling{
    retainSendOnSub = 0, /**< Send retained messages at the time of subscription. */
    retainSendOnSubIfNotPresent = 1,  /**< Send retained messages at subscription only if subscription does not currently exist. */
    retainDoNotSendonSub = 2 /**< Do not send retained messages at the time of subscription. */
}MQTTRetainHandling_t;

/**
 * @ingroup mqtt_struct_types
 * @brief MQTT SUBSCRIBE packet parameters.
 */
typedef struct MQTTSubscribeInfo
{
    /**
     * @brief Quality of Service for subscription. Include protocol error of qos > 2
     */
    MQTTQoS_t qos;

    /**
     * @brief Topic filter to subscribe to.
     */
    const char * pTopicFilter;

    /**
     * @brief Length of subscription topic filter - unsigned long
     */
    size_t topicFilterLength;
    /**
     * @brief no local option for subscription. Include protocol error if noLocalOption = 1 in a shared subscription
     */

    /**
     * @brief If true, Application Messages that are published to this subscription
     * will not be forwarded to the Client that published them.
     */
    bool noLocalOption;

    /**
     *  @brief If true, Application Messages forwarded using this subscription keep the RETAIN
     * flag they were published with.
     */
    bool retainAsPublishedOption;

    /**
     * @brief Specifies whether retained messages are sent
     * when the subscription is established.
     */
    MQTTRetainHandling_t retainHandlingOption;

} MQTTSubscribeInfo_t;

/**
 * @ingroup mqtt_struct_types
 * @brief MQTT PUBLISH packet parameters.
 */
typedef struct MQTTPublishInfo
{
    /**
     * @brief Quality of Service for message.
     */
    MQTTQoS_t qos;

    /**
     * @brief Whether this is a retained message.
     */
    bool retain;

    /**
     * @brief Whether this is a duplicate publish message.
     */
    bool dup;

    /**
     * @brief Topic name on which the message is published.
     */
    const char * pTopicName;

    /**
     * @brief Length of topic name.
     */
    size_t topicNameLength;

    /**
     * @brief Message payload.
     */
    const void * pPayload;

    /**
     * @brief Message payload length.
     */
    size_t payloadLength;

     /**
     * @brief Length of the properties.
     */
    size_t propertyLength;

} MQTTPublishInfo_t;

/**
 * @ingroup mqtt_struct_types
 * @brief MQTT incoming packet parameters.
 */
typedef struct MQTTPacketInfo
{
    /**
     * @brief Type of incoming MQTT packet.
     */
    uint8_t type;

    /**
     * @brief Remaining serialized data in the MQTT packet.
     */
    uint8_t * pRemainingData;

    /**
     * @brief Length of remaining serialized data.
     */
    uint32_t remainingLength;

    /**
     * @brief The length of the MQTT header including the type and length.
     */
    size_t headerLength;
} MQTTPacketInfo_t;

/**
 * @ingroup mqtt_struct_types
 * @brief Property builder for MQTT packets.
 */
typedef struct MQTTPropBuilder
{
    uint8_t * pBuffer;           /**< @brief Pointer to the buffer for storing properties. */
    size_t bufferLength;         /**< @brief Total length of the buffer available for properties. */
    size_t currentIndex;       /**< @brief Current position in the buffer where next property will be written. */
    uint32_t fieldSet;           /**< @brief Bitfield tracking which properties have been added. */
} MQTTPropBuilder_t;

 /**
 * @ingroup mqtt_struct_types
 * @brief Struct to hold reason codes.
 */
typedef struct MQTTReasonCodeInfo
{
    /** @brief Pointer to the reason code array. */
    const uint8_t * reasonCode;

    /** @brief Length of the reason code array. */
    size_t reasonCodeLength;

} MQTTReasonCodeInfo_t;

/**
* @ingroup mqtt_struct_types
* @brief Struct to hold connect and connack properties.
*/
typedef struct MQTTConnectProperties
{
     /**
     * @brief Four Byte Integer representing the Session Expiry Interval in seconds.
     */
    uint32_t sessionExpiry;

     /**
     * @brief Maximum number of unacknowledged PUBLISH packets client is willing to receive.
     */
    uint16_t receiveMax;

     /**
     * @brief Four Byte Integer representing the Maximum Packet Size the Client is willing to accept.
     */
    uint32_t maxPacketSize;

     /**
     * @brief Two Byte Integer representing the Topic Alias Maximum value.
     */
    uint16_t topicAliasMax;

     /**
     * @brief  A value of 0 indicates that the Server MUST NOT return Response Information.
     */
    bool  requestResponseInfo;

     /**
     * @brief The Client uses this value to indicate whether the Reason String or User Properties
     *  are sent in the case of failures
     */
    bool  requestProblemInfo;

    /**
     * @brief Maximum number of unacknowledged PUBLISH packets server is willing to receive.
     */
    uint16_t serverReceiveMax;

     /**
     * @brief  Max qos supported by the server.
     */
    uint8_t serverMaxQos;

     /**
     * @brief Byte declares whether the Server supports retained messages.
     */
    uint8_t retainAvailable;

     /**
     * @brief Four Byte Integer representing the Maximum Packet Size the Server is willing to accept.
     */
    uint32_t serverMaxPacketSize;

     /**
     * @brief Two Byte Integer representing the Topic Alias Maximum value.
     */
    uint16_t serverTopicAliasMax;

     /**
     * @brief Whether wildcard subscription is available.
     */
    uint8_t isWildcardAvailable;

     /**
     * @brief Whether the Server supports Subscription Identifiers.
     */
    uint8_t isSubscriptionIdAvailable;

     /**
     * @brief Whether the Server supports Shared Subscription.
     */
    uint8_t isSharedAvailable;

     /**
     * @brief Keep Alive value given by the server.
     */
    uint16_t serverKeepAlive;


} MQTTConnectionProperties_t;

/**
 * @ingroup mqtt_enum_types
 * @brief MQTT reason codes.
 *
 * These values are defined in the MQTT 5.0 specification.
 */
typedef enum MQTTSuccessFailReasonCode
{
    /* PUBACK reason codes */
    MQTT_REASON_PUBACK_SUCCESS = 0x00U,                    /**< Publish was successfully received and accepted. */
    MQTT_REASON_PUBACK_NO_MATCHING_SUBSCRIBERS = 0x10U,    /**< Publish was accepted but there are no subscribers. */
    MQTT_REASON_PUBACK_UNSPECIFIED_ERROR = 0x80U,         /**< Unspecified error occurred for the PUBACK. */
    MQTT_REASON_PUBACK_IMPLEMENTATION_SPECIFIC_ERROR = 0x83U, /**< Implementation specific error for the PUBACK. */
    MQTT_REASON_PUBACK_NOT_AUTHORIZED = 0x87U,            /**< Client is not authorized to publish. */
    MQTT_REASON_PUBACK_TOPIC_NAME_INVALID = 0x90U,        /**< Topic name is not valid. */
    MQTT_REASON_PUBACK_PACKET_IDENTIFIER_IN_USE = 0x91U,  /**< Packet identifier is already in use. */
    MQTT_REASON_PUBACK_QUOTA_EXCEEDED = 0x97U,            /**< Implementation or system quota exceeded. */
    MQTT_REASON_PUBACK_PAYLOAD_FORMAT_INVALID = 0x99U,    /**< Payload format is invalid. */

    /* PUBREC reason codes */
    MQTT_REASON_PUBREC_SUCCESS = 0x00U,                   /**< Publish was successfully received for QoS 2. */
    MQTT_REASON_PUBREC_NO_MATCHING_SUBSCRIBERS = 0x10U,   /**< Publish received but no matching subscribers. */
    MQTT_REASON_PUBREC_UNSPECIFIED_ERROR = 0x80U,        /**< Unspecified error occurred for the PUBREC. */
    MQTT_REASON_PUBREC_IMPLEMENTATION_SPECIFIC_ERROR = 0x83U, /**< Implementation specific error for the PUBREC. */
    MQTT_REASON_PUBREC_NOT_AUTHORIZED = 0x87U,           /**< Client is not authorized to publish. */
    MQTT_REASON_PUBREC_TOPIC_NAME_INVALID = 0x90U,       /**< Topic name is not valid. */
    MQTT_REASON_PUBREC_PACKET_IDENTIFIER_IN_USE = 0x91U, /**< Packet identifier is already in use. */
    MQTT_REASON_PUBREC_QUOTA_EXCEEDED = 0x97U,           /**< Implementation or system quota exceeded. */
    MQTT_REASON_PUBREC_PAYLOAD_FORMAT_INVALID = 0x99U,   /**< Payload format is invalid. */

    /* PUBREL reason codes */
    MQTT_REASON_PUBREL_SUCCESS = 0x00U,                  /**< Publish release was successful. */
    MQTT_REASON_PUBREL_PACKET_IDENTIFIER_NOT_FOUND = 0x92U, /**< Packet identifier was not found. */

    /* PUBCOMP reason codes */
    MQTT_REASON_PUBCOMP_SUCCESS = 0x00U,                 /**< Publish complete was successful. */
    MQTT_REASON_PUBCOMP_PACKET_IDENTIFIER_NOT_FOUND = 0x92U, /**< Packet identifier was not found. */

    /* CONNACK reason codes */
    MQTT_REASON_CONNACK_SUCCESS = 0x00U,                 /**< Connection accepted. */
    MQTT_REASON_CONNACK_UNSPECIFIED_ERROR = 0x80U,       /**< Unspecified error occurred during connection. */
    MQTT_REASON_CONNACK_MALFORMED_PACKET = 0x81U,        /**< Received packet was malformed. */
    MQTT_REASON_CONNACK_PROTOCOL_ERROR = 0x82U,          /**< Protocol error occurred. */
    MQTT_REASON_CONNACK_IMPLEMENTATION_SPECIFIC_ERROR = 0x83U, /**< Implementation specific error. */
    MQTT_REASON_CONNACK_UNSUPPORTED_PROTOCOL_VERSION = 0x84U, /**< Protocol version not supported. */
    MQTT_REASON_CONNACK_CLIENT_IDENTIFIER_NOT_VALID = 0x85U, /**< Client identifier is not valid. */
    MQTT_REASON_CONNACK_BAD_USER_NAME_OR_PASSWORD = 0x86U, /**< Username or password is malformed. */
    MQTT_REASON_CONNACK_NOT_AUTHORIZED = 0x87U,          /**< Client is not authorized to connect. */
    MQTT_REASON_CONNACK_SERVER_UNAVAILABLE = 0x88U,      /**< Server is unavailable. */
    MQTT_REASON_CONNACK_SERVER_BUSY = 0x89U,             /**< Server is busy. */
    MQTT_REASON_CONNACK_BANNED = 0x8AU,                  /**< Client has been banned. */
    MQTT_REASON_CONNACK_BAD_AUTHENTICATION_METHOD = 0x8CU, /**< Authentication method is not supported. */
    MQTT_REASON_CONNACK_TOPIC_NAME_INVALID = 0x90U,      /**< Topic name is invalid. */
    MQTT_REASON_CONNACK_PACKET_TOO_LARGE = 0x95U,        /**< Packet size exceeds maximum allowed. */
    MQTT_REASON_CONNACK_QUOTA_EXCEEDED = 0x97U,          /**< Implementation or system quota exceeded. */
    MQTT_REASON_CONNACK_PAYLOAD_FORMAT_INVALID = 0x99U,  /**< Payload format is invalid. */
    MQTT_REASON_CONNACK_RETAIN_NOT_SUPPORTED = 0x9AU,    /**< Retain is not supported. */
    MQTT_REASON_CONNACK_QOS_NOT_SUPPORTED = 0x9BU,       /**< QoS level is not supported. */
    MQTT_REASON_CONNACK_USE_ANOTHER_SERVER = 0x9CU,      /**< Client should temporarily use another server. */
    MQTT_REASON_CONNACK_SERVER_MOVED = 0x9DU,            /**< Client should permanently use another server. */
    MQTT_REASON_CONNACK_CONNECTION_RATE_EXCEEDED = 0x9FU, /**< Connection rate limit exceeded. */

    /* SUBACK reason codes */
    MQTT_REASON_SUBACK_GRANTED_QOS0 = 0x00U,             /**< Subscription accepted with maximum QoS 0. */
    MQTT_REASON_SUBACK_GRANTED_QOS1 = 0x01U,             /**< Subscription accepted with maximum QoS 1. */
    MQTT_REASON_SUBACK_GRANTED_QOS2 = 0x02U,             /**< Subscription accepted with maximum QoS 2. */
    MQTT_REASON_SUBACK_UNSPECIFIED_ERROR = 0x80U,        /**< Unspecified error occurred for the subscription. */
    MQTT_REASON_SUBACK_IMPLEMENTATION_SPECIFIC_ERROR = 0x83U, /**< Implementation specific error. */
    MQTT_REASON_SUBACK_NOT_AUTHORIZED = 0x87U,           /**< Client is not authorized to subscribe. */
    MQTT_REASON_SUBACK_TOPIC_FILTER_INVALID = 0x8FU,     /**< Topic filter is not valid. */
    MQTT_REASON_SUBACK_PACKET_IDENTIFIER_IN_USE = 0x91U, /**< Packet identifier is already in use. */
    MQTT_REASON_SUBACK_QUOTA_EXCEEDED = 0x97U,           /**< Implementation or system quota exceeded. */
    MQTT_REASON_SUBACK_SHARED_SUBSCRIPTIONS_NOT_SUPPORTED = 0x9EU, /**< Shared subscriptions are not supported. */
    MQTT_REASON_SUBACK_SUBSCRIPTION_IDENTIFIERS_NOT_SUPPORTED = 0xA1U, /**< Subscription identifiers are not supported. */
    MQTT_REASON_SUBACK_WILDCARD_SUBSCRIPTIONS_NOT_SUPPORTED = 0xA2U, /**< Wildcard subscriptions are not supported. */

    /* UNSUBACK reason codes */
    MQTT_REASON_UNSUBACK_SUCCESS = 0x00U,                /**< Unsubscribe was successful. */
    MQTT_REASON_UNSUBACK_NO_SUBSCRIPTION_EXISTED = 0x11U, /**< No matching subscription existed. */
    MQTT_REASON_UNSUBACK_UNSPECIFIED_ERROR = 0x80U,      /**< Unspecified error occurred for the unsubscribe. */
    MQTT_REASON_UNSUBACK_IMPLEMENTATION_SPECIFIC_ERROR = 0x83U, /**< Implementation specific error. */
    MQTT_REASON_UNSUBACK_NOT_AUTHORIZED = 0x87U,         /**< Client is not authorized to unsubscribe. */
    MQTT_REASON_UNSUBACK_TOPIC_FILTER_INVALID = 0x8FU,   /**< Topic filter is not valid. */
    MQTT_REASON_UNSUBACK_PACKET_IDENTIFIER_IN_USE = 0x91U, /**< Packet identifier is already in use. */

    /* DISCONNECT reason codes */
    MQTT_REASON_DISCONNECT_NORMAL_DISCONNECTION = 0x00U,  /**< Normal client-initiated disconnect. */
    MQTT_REASON_DISCONNECT_DISCONNECT_WITH_WILL_MESSAGE = 0x04U, /**< Client disconnecting with Will Message. */
    MQTT_REASON_DISCONNECT_UNSPECIFIED_ERROR = 0x80U,     /**< Unspecified error occurred. */
    MQTT_REASON_DISCONNECT_MALFORMED_PACKET = 0x81U,      /**< Received packet was malformed. */
    MQTT_REASON_DISCONNECT_PROTOCOL_ERROR = 0x82U,        /**< Protocol error occurred. */
    MQTT_REASON_DISCONNECT_IMPLEMENTATION_SPECIFIC_ERROR = 0x83U, /**< Implementation specific error. */
    MQTT_REASON_DISCONNECT_NOT_AUTHORIZED = 0x87U,        /**< Client is not authorized. */
    MQTT_REASON_DISCONNECT_SERVER_BUSY = 0x89U,           /**< Server is busy. */
    MQTT_REASON_DISCONNECT_SERVER_SHUTTING_DOWN = 0x8BU,  /**< Server is shutting down. */
    MQTT_REASON_DISCONNECT_BAD_AUTHENTICATION_METHOD = 0x8CU, /**< Authentication method is invalid. */
    MQTT_REASON_DISCONNECT_KEEP_ALIVE_TIMEOUT = 0x8DU,    /**< Keep alive timeout occurred. */
    MQTT_REASON_DISCONNECT_SESSION_TAKEN_OVER = 0x8EU,    /**< Another connection using same client ID. */
    MQTT_REASON_DISCONNECT_TOPIC_FILTER_INVALID = 0x8FU,  /**< Topic filter is not valid. */
    MQTT_REASON_DISCONNECT_TOPIC_NAME_INVALID = 0x90U,    /**< Topic name is not valid. */
    MQTT_REASON_DISCONNECT_RECEIVE_MAXIMUM_EXCEEDED = 0x93U, /**< Receive maximum value exceeded. */
    MQTT_REASON_DISCONNECT_TOPIC_ALIAS_INVALID = 0x94U,   /**< Topic alias is invalid. */
    MQTT_REASON_DISCONNECT_PACKET_TOO_LARGE = 0x95U,      /**< Packet size exceeds maximum allowed. */
    MQTT_REASON_DISCONNECT_MESSAGE_RATE_TOO_HIGH = 0x96U, /**< Message rate too high. */
    MQTT_REASON_DISCONNECT_QUOTA_EXCEEDED = 0x97U,        /**< Implementation or system quota exceeded. */
    MQTT_REASON_DISCONNECT_ADMINISTRATIVE_ACTION = 0x98U,  /**< Disconnected due to administrative action. */
    MQTT_REASON_DISCONNECT_PAYLOAD_FORMAT_INVALID = 0x99U, /**< Payload format is invalid. */
    MQTT_REASON_DISCONNECT_RETAIN_NOT_SUPPORTED = 0x9AU,   /**< Retain is not supported. */
    MQTT_REASON_DISCONNECT_QOS_NOT_SUPPORTED = 0x9BU,      /**< QoS level is not supported. */
    MQTT_REASON_DISCONNECT_USE_ANOTHER_SERVER = 0x9CU,     /**< Client should temporarily use another server. */
    MQTT_REASON_DISCONNECT_SERVER_MOVED = 0x9DU,           /**< Client should permanently use another server. */
    MQTT_REASON_DISCONNECT_SHARED_SUBSCRIPTIONS_NOT_SUPPORTED = 0x9EU, /**< Shared subscriptions are not supported. */
    MQTT_REASON_DISCONNECT_CONNECTION_RATE_EXCEEDED = 0x9FU, /**< Connection rate limit exceeded. */
    MQTT_REASON_DISCONNECT_MAXIMUM_CONNECT_TIME = 0xA0U,    /**< Maximum connection time authorized exceeded. */
    MQTT_REASON_DISCONNECT_SUBSCRIPTION_IDENTIFIERS_NOT_SUPPORTED = 0xA1U, /**< Subscription identifiers are not supported. */
    MQTT_REASON_DISCONNECT_WILDCARD_SUBSCRIPTIONS_NOT_SUPPORTED = 0xA2U,    /**< Wildcard subscriptions are not supported. */

    MQTT_INVALID_REASON_CODE = 0xFF /**< @brief Invalid reason code. */

} MQTTSuccessFailReasonCode_t;

/**
* @ingroup mqtt_struct_types
* @brief Struct to hold user property.
*/
typedef struct MQTTUserProperty
{
    /**
    * @brief key.
    */
    const char * pKey;
    /**
    * @brief Length of the key.
    */
    size_t keyLength;
    /**
    * @brief value.
    */
    const char * pValue;
    /**
    * @brief Length of the value.
    */
    size_t valueLength;
} MQTTUserProperty_t;

/**
 * @ingroup mqtt_enum_types
 * @brief MQTT Subscription packet types.
 */
typedef enum MQTTSubscriptionType
{
    MQTT_TYPE_SUBSCRIBE,  /**< @brief The type is a SUBSCRIBE packet. */
    MQTT_TYPE_UNSUBSCRIBE /**< @brief The type is a UNSUBSCRIBE packet. */
} MQTTSubscriptionType_t;

/**
 * @brief Get the size and Remaining Length of an MQTT Version 5 CONNECT packet.
 *
 * This function must be called before #MQTT_SerializeConnect in order to get
 * the size of the MQTT CONNECT packet that is generated from #MQTTConnectInfo_t, #MQTTPublishInfo_t
 * and optional MQTTPropBuilder_t. The size of the #MQTTFixedBuffer_t supplied
 * to #MQTT_SerializeConnect must be at least @p pPacketSize. The provided
 * @p pConnectInfo and @p pWillInfo are valid for serialization with
 * #MQTT_SerializeConnect only if this function returns #MQTTSuccess. The
 * remaining length returned in @p pRemainingLength and the packet size returned
 * in @p pPacketSize are valid only if this function returns #MQTTSuccess.
 *
 * @param[in] pConnectInfo MQTT CONNECT packet parameters.
 * @param[in] pWillInfo Last Will and Testament. Pass NULL if not used.
 * @param[in] pConnectProperties MQTT CONNECT properties builder. Pass NULL if not used.
 * @param[in] pWillProperties MQTT Will properties builder. Pass NULL if not used.
 * @param[out] pRemainingLength The Remaining Length of the MQTT CONNECT packet.
 * @param[out] pPacketSize The total size of the MQTT CONNECT packet.
 *
 * @return #MQTTBadParameter if the packet would exceed the size allowed by the
 * MQTT spec; #MQTTSuccess otherwise.
 *
 * <b>Example</b>
 * @code{c}
 *
 * // Variables used in this example.
 * MQTTStatus_t status;
 * MQTTConnectInfo_t connectInfo = { 0 };
 * MQTTPublishInfo_t willInfo = { 0 };
 * MQTTPropBuilder_t connectionProperties = { 0 };
 * MQTTPropBuilder_t willProperties = { 0 };
 * size_t remainingLength = 0, packetSize = 0;
 *
 * // Initialize the connection info, the details are out of scope for this example.
 * initializeConnectInfo( &connectInfo );
 *
 * // Initialize the optional will info, the details are out of scope for this example.
 * initializeWillInfo( &willInfo );
 *
 * // Initialize connect properties and will properties, the details are out of scope for this example.
 * initializeConnectProperties( &connectionProperties );
 * initializeWillProperties( &willProperties );
 *
 * // Get the size requirement for the connect packet.
 * status = MQTT_GetConnectPacketSize(
 *      &connectInfo,
 *      &willInfo,
 *      &connectionProperties,
 *      &willProperties,
 *      &remainingLength,
 *      &packetSize
 * );
 *
 * if( status == MQTTSuccess )
 * {
 *      // The application should allocate or use a static #MQTTFixedBuffer_t
 *      // of size >= packetSize to serialize the connect request.
 * }
 * @endcode
 */
/* @[declare_mqtt_getconnectpacketsize] */
MQTTStatus_t MQTT_GetConnectPacketSize( const MQTTConnectInfo_t * pConnectInfo,
                                        const MQTTPublishInfo_t * pWillInfo,
                                        const MQTTPropBuilder_t * pConnectProperties,
                                        const MQTTPropBuilder_t * pWillProperties,
                                        uint32_t * pRemainingLength,
                                        uint32_t * pPacketSize );
/* @[declare_mqtt_getconnectpacketsize] */

/**
 * @brief Serialize an MQTT CONNECT packet in the given fixed buffer @p pFixedBuffer.
 *
 * #MQTT_GetConnectPacketSize should be called with @p pConnectInfo, @p pWillInfo,
 * @p pConnectProperties, and @p pWillProperties before invoking this function to get
 * the size of the required #MQTTFixedBuffer_t and @p remainingLength. The
 * @p remainingLength must be the same as returned by #MQTT_GetConnectPacketSize.
 * The #MQTTFixedBuffer_t must be at least as large as the size returned by
 * #MQTT_GetConnectPacketSize.
 *
 * @param[in] pConnectInfo MQTT CONNECT packet parameters.
 * @param[in] pWillInfo Last Will and Testament. Pass NULL if not used.
 * @param[in] pConnectProperties MQTT CONNECT properties builder. Pass NULL if not used.
 * @param[in] pWillProperties MQTT Will properties builder. Pass NULL if not used.
 * @param[in] remainingLength Remaining Length provided by #MQTT_GetConnectPacketSize.
 * @param[out] pFixedBuffer Buffer for packet serialization.
 *
 * @return #MQTTNoMemory if pFixedBuffer is too small to hold the MQTT packet;
 * #MQTTBadParameter if invalid parameters are passed;
 * #MQTTSuccess otherwise.
 *
 * <b>Example</b>
 * @code{c}
 *
 * // Variables used in this example.
 * MQTTStatus_t status;
 * MQTTConnectInfo_t connectInfo = { 0 };
 * MQTTPublishInfo_t willInfo = { 0 };
 * MQTTPropBuilder_t connectionProperties = { 0 };
 * MQTTPropBuilder_t willProperties = { 0 };
 * MQTTFixedBuffer_t fixedBuffer;
 * uint8_t buffer[ BUFFER_SIZE ];
 * size_t remainingLength = 0, packetSize = 0;
 *
 * fixedBuffer.pBuffer = buffer;
 * fixedBuffer.size = BUFFER_SIZE;
 *
 * // Assume connectInfo, willInfo, and properties are initialized.
 * // Get the size requirement for the connect packet.
 * status = MQTT_GetConnectPacketSize(
 *      &connectInfo, &willInfo, &connectionProperties, &willProperties,
 *      &remainingLength, &packetSize
 * );
 * assert( status == MQTTSuccess );
 * assert( packetSize <= BUFFER_SIZE );
 *
 * // Serialize the connect packet into the fixed buffer.
 * status = MQTT_SerializeConnect(
 *      &connectInfo,
 *      &willInfo,
 *      &connectionProperties,
 *      &willProperties,
 *      remainingLength,
 *      &fixedBuffer
 * );
 *
 * if( status == MQTTSuccess )
 * {
 *      // The connect packet can now be sent to the broker.
 * }
 * @endcode
 */
/* @[declare_mqtt_serializeconnect] */
MQTTStatus_t MQTT_SerializeConnect( const MQTTConnectInfo_t * pConnectInfo,
                                    const MQTTPublishInfo_t * pWillInfo,
                                    const MQTTPropBuilder_t * pConnectProperties,
                                    const MQTTPropBuilder_t * pWillProperties,
                                    uint32_t remainingLength,
                                    const MQTTFixedBuffer_t * pFixedBuffer );
/* @[declare_mqtt_serializeconnect] */

/**
 * @brief Get packet size and Remaining Length of an MQTT SUBSCRIBE packet.
 *
 * This function must be called before #MQTT_SerializeSubscribe in order to get
 * the size of the MQTT SUBSCRIBE packet that is generated from the list of
 * #MQTTSubscribeInfo_t and #MQTTPropBuilder_t (optional subscribe properties).
 * The size of the #MQTTFixedBuffer_t supplied to #MQTT_SerializeSubscribe must
 * be at least @p pPacketSize. The provided @p pSubscriptionList is valid for
 * serialization with #MQTT_SerializeSubscribe
 * only if this function returns #MQTTSuccess. The remaining length returned in
 * @p pRemainingLength and the packet size returned in @p pPacketSize are valid
 * only if this function returns #MQTTSuccess.
 *
 * @param[in] pSubscriptionList List of MQTT subscription info.
 * @param[in] subscriptionCount The number of elements in pSubscriptionList.
 * @param[in] pSubscribeProperties MQTT SUBSCRIBE properties builder. Pass NULL if not used.
 * @param[out] pRemainingLength The Remaining Length of the MQTT SUBSCRIBE packet.
 * @param[out] pPacketSize The total size of the MQTT SUBSCRIBE packet.
 * @param[in] maxPacketSize Maximum packet size.
 *
 * @return #MQTTBadParameter if the packet would exceed the size allowed by the
 * MQTT spec; #MQTTSuccess otherwise.
 *
 * <b>Example</b>
 * @code{c}
 *
 * // Variables used in this example.
 * MQTTStatus_t status;
 * MQTTSubscribeInfo_t subscriptionList[ NUMBER_OF_SUBSCRIPTIONS ] = { 0 };
 * MQTTPropBuilder_t subscribeProperties = { 0 };
 * size_t remainingLength = 0, packetSize = 0;
 * // This is assumed to be a list of filters we want to subscribe to.
 * const char * filters[ NUMBER_OF_SUBSCRIPTIONS ];
 *
 * // Set each subscription.
 * for( int i = 0; i < NUMBER_OF_SUBSCRIPTIONS; i++ )
 * {
 *      subscriptionList[ i ].qos = MQTTQoS0;
 *      // Each subscription needs a topic filter.
 *      subscriptionList[ i ].pTopicFilter = filters[ i ];
 *      subscriptionList[ i ].topicFilterLength = strlen( filters[ i ] );
 *      subscriptionList[ i ].noLocalOption = false;
 *      subscriptionList[ i ].retainAsPublishedOption = false;
 *      subscriptionList[ i ].retainHandlingOption = retainSendOnSub;
 * }
 *
 * // Initialize subscribe properties (if needed)
 * initializeSubscribeProperties( &subscribeProperties );
 *
 * // Get the size requirement for the subscribe packet.
 * status = MQTT_GetSubscribePacketSize(
 *      &subscriptionList[ 0 ],
 *      NUMBER_OF_SUBSCRIPTIONS,
 *      &subscribeProperties,
 *      &remainingLength,
 *      &packetSize,
 *      maxPacketSize
 * );
 *
 * if( status == MQTTSuccess )
 * {
 *      // The application should allocate or use a static #MQTTFixedBuffer_t
 *      // of size >= packetSize to serialize the subscribe request.
 * }
 * @endcode
 */
/* @[declare_mqtt_getsubscribepacketsize] */
MQTTStatus_t MQTT_GetSubscribePacketSize( const MQTTSubscribeInfo_t * pSubscriptionList,
                                          size_t subscriptionCount,
                                          const MQTTPropBuilder_t * pSubscribeProperties,
                                          uint32_t * pRemainingLength,
                                          uint32_t * pPacketSize,
                                          uint32_t maxPacketSize );
/* @[declare_mqtt_getsubscribepacketsize] */

/**
 * @brief Serialize an MQTT SUBSCRIBE packet in the given buffer.
 *
 * #MQTT_GetSubscribePacketSize should be called with @p pSubscriptionList
 * before invoking this function to get the size of the required
 * #MQTTFixedBuffer_t and @p remainingLength. The @p remainingLength must be
 * the same as returned by #MQTT_GetSubscribePacketSize. The #MQTTFixedBuffer_t
 * must be at least as large as the size returned by #MQTT_GetSubscribePacketSize.
 *
 * @param[in] pSubscriptionList List of MQTT subscription info.
 * @param[in] subscriptionCount The number of elements in pSubscriptionList.
 * @param[in] pSubscribeProperties MQTT v5.0 properties for the SUBSCRIBE packet. Can be NULL
 * if no properties are needed.
 * @param[in] packetId packet ID generated by #MQTT_GetPacketId.
 * @param[in] remainingLength Remaining Length provided by #MQTT_GetSubscribePacketSize.
 * @param[out] pFixedBuffer Buffer for packet serialization.
 *
 * @return #MQTTNoMemory if pFixedBuffer is too small to hold the MQTT packet;
 * #MQTTBadParameter if invalid parameters are passed;
 * #MQTTSuccess otherwise.
 *
 * <b>Example</b>
 * @code{c}
 *
 * // Variables used in this example.
 * MQTTStatus_t status;
 * MQTTSubscribeInfo_t subscriptionList[ NUMBER_OF_SUBSCRIPTIONS ] = { 0 };
 * MQTTPropBuilder_t subscribeProperties = { 0 };
 * MQTTFixedBuffer_t fixedBuffer;
 * uint8_t buffer[ BUFFER_SIZE ];
 * size_t remainingLength = 0, packetSize = 0;
 * uint16_t packetId;
 *
 * fixedBuffer.pBuffer = buffer;
 * fixedBuffer.size = BUFFER_SIZE;
 *
 * // Function to return a valid, unused packet identifier. The details are out of
 * // scope for this example.
 * packetId = getNewPacketId();
 *
 * // Assume subscriptionList and subscribeProperties have been initialized.
 * Get the subscribe packet size.
 * status = MQTT_GetSubscribePacketSize(
 *      &subscriptionList[ 0 ], NUMBER_OF_SUBSCRIPTIONS, &subscribeProperties,
 *      &remainingLength, &packetSize
 * );
 * assert( status == MQTTSuccess );
 * assert( packetSize <= BUFFER_SIZE );
 *
 * // Serialize the subscribe packet into the fixed buffer.
 * status = MQTT_SerializeSubscribe(
 *      &subscriptionList[ 0 ],
 *      NUMBER_OF_SUBSCRIPTIONS,
 *      &subscribeProperties,
 *      packetId,
 *      remainingLength,
 *      &fixedBuffer
 * );
 *
 * if( status == MQTTSuccess )
 * {
 *      // The subscribe packet can now be sent to the broker.
 * }
 * @endcode
 */
/* @[declare_mqtt_serializesubscribe] */
MQTTStatus_t MQTT_SerializeSubscribe( const MQTTSubscribeInfo_t * pSubscriptionList,
                                      size_t subscriptionCount,
                                      const MQTTPropBuilder_t * pSubscribeProperties,
                                      uint16_t packetId,
                                      uint32_t remainingLength,
                                      const MQTTFixedBuffer_t * pFixedBuffer );
/* @[declare_mqtt_serializesubscribe] */

/**
 * @brief Get packet size and Remaining Length of an MQTT UNSUBSCRIBE packet.
 *
 * This function must be called before #MQTT_SerializeUnsubscribe in order to
 * get the size of the MQTT UNSUBSCRIBE packet that is generated from the list
 * of #MQTTSubscribeInfo_t and #MQTTPropBuilder_t (optional unsubscribe properties).
 * The size of the #MQTTFixedBuffer_t supplied to #MQTT_SerializeUnsubscribe must be
 * at least @p pPacketSize. The provided @p pSubscriptionList is valid for serialization
 * with #MQTT_SerializeUnsubscribe only if this function returns #MQTTSuccess.
 * The remaining length returned in @p pRemainingLength and the packet size returned
 * in @p pPacketSize are valid only if this function returns #MQTTSuccess.
 *
 * @param[in] pSubscriptionList List of MQTT subscription info.
 * @param[in] subscriptionCount The number of elements in pSubscriptionList.
 * @param[in] pUnsubscribeProperties MQTT UNSUBSCRIBE properties builder. Pass NULL if not used.
 * @param[out] pRemainingLength The Remaining Length of the MQTT UNSUBSCRIBE packet.
 * @param[out] pPacketSize The total size of the MQTT UNSUBSCRIBE packet.
 * @param[in] maxPacketSize Maximum packet size.
 *
 * @return #MQTTBadParameter if the packet would exceed the size allowed by the
 * MQTT spec; #MQTTSuccess otherwise.
 *
 * <b>Example</b>
 * @code{c}
 *
 * // Variables used in this example.
 * MQTTStatus_t status;
 * MQTTSubscribeInfo_t subscriptionList[ NUMBER_OF_SUBSCRIPTIONS ] = { 0 };
 * size_t remainingLength = 0, packetSize = 0;
 * MQTTPropBuilder_t unsubscribeProperties = { 0 };
 * size_t maxPacketSize = 0;
 *
 * // Initialize maxPacketSize. The details are out of scope for this example.
 * initializeMaxPacketSize( &maxPacketSize );
 *
 * // Initialize the subscribe info. The details are out of scope for this example.
 * initializeSubscribeInfo( &subscriptionList[ 0 ] );
 *
 * //Initialize the property buffer. The details are out of scope for this example.
 * initializePropertyBuffer( &unsubscribeProperties );
 *
 * // Get the size requirement for the unsubscribe packet.
 * status = MQTT_GetUnsubscribePacketSize(
 *      &subscriptionList[ 0 ],
 *      NUMBER_OF_SUBSCRIPTIONS,
 *      &unsubscribeProperties,
 *      &remainingLength,
 *      &packetSize,
 *      maxPacketSize);
 *
 * if( status == MQTTSuccess )
 * {
 *      // The unsubscribe packet can now be sent to the broker.
 * }
 * @endcode
 */
/* @[declare_mqtt_getunsubscribepacketsize] */
MQTTStatus_t MQTT_GetUnsubscribePacketSize( const MQTTSubscribeInfo_t * pSubscriptionList,
                                            size_t subscriptionCount,
                                            const MQTTPropBuilder_t * pUnsubscribeProperties,
                                            uint32_t * pRemainingLength,
                                            uint32_t * pPacketSize,
                                            uint32_t maxPacketSize );
/* @[declare_mqtt_getunsubscribepacketsize] */

/**
 * @brief Serialize an MQTT UNSUBSCRIBE packet with properties in the given buffer.
 *
 * #MQTT_GetUnsubscribePacketSize should be called with @p pSubscriptionList
 * and @p pUnsubscribeProperties before invoking this function to get the size of the required
 * #MQTTFixedBuffer_t and @p remainingLength. The @p remainingLength must be
 * the same as returned by #MQTT_GetUnsubscribePacketSize. The #MQTTFixedBuffer_t
 * must be at least as large as the size returned by #MQTT_GetUnsubscribePacketSize.
 *
 * @param[in] pSubscriptionList List of MQTT subscription info to unsubscribe from.
 * @param[in] subscriptionCount The number of elements in pSubscriptionList.
 * @param[in] pUnsubscribeProperties MQTT 5.0 properties for the UNSUBSCRIBE packet. Can be NULL if no properties are needed.
 * @param[in] packetId Packet identifier used for the UNSUBSCRIBE packet.
 * @param[in] remainingLength Remaining Length provided by #MQTT_GetUnsubscribePacketSize.
 * @param[out] pFixedBuffer Buffer where the serialized UNSUBSCRIBE packet will be written.
 *
 * @return #MQTTNoMemory if pFixedBuffer is too small to hold the MQTT packet;
 * #MQTTBadParameter if any of the parameters are invalid (NULL pSubscriptionList or pFixedBuffer, zero subscriptionCount);
 * #MQTTSuccess if the packet was serialized successfully.
 *
 * <b>Example</b>
 * @code{c}
 *
 * // Variables used in this example.
 * MQTTStatus_t status;
 * MQTTSubscribeInfo_t subscriptionList[2];
 * MQTTPropBuilder_t unsubscribeProperties;
 * MQTTFixedBuffer_t fixedBuffer;
 * uint8_t buffer[100];
 * size_t remainingLength = 0, packetSize = 0;
 * uint16_t packetId = 1;
 *
 * // Initialize the fixed buffer.
 * fixedBuffer.pBuffer = buffer;
 * fixedBuffer.size = sizeof( buffer );
 *
 * // Initialize subscription list.
 * subscriptionList[0].pTopicFilter = "topic/1";
 * subscriptionList[0].topicFilterLength = strlen("topic/1");
 * subscriptionList[1].pTopicFilter = "topic/2";
 * subscriptionList[1].topicFilterLength = strlen("topic/2");
 *
 * // Initialize properties (optional)
 *
 * // Get size requirement for the unsubscribe packet.
 * status = MQTT_GetUnsubscribePacketSize(
 *      subscriptionList,
 *      2,
 *      &unsubscribeProperties,
 *      &remainingLength,
 *      &packetSize
 * );
 *
 * if( status == MQTTSuccess )
 * {
 *      // Serialize unsubscribe packet.
 *      status = MQTT_SerializeUnsubscribe(
 *          subscriptionList,
 *          2,
 *          &unsubscribeProperties,
 *          packetId,
 *          remainingLength,
 *          &fixedBuffer
 *      );
 * }
 *
 * if( status == MQTTSuccess )
 * {
 *      // The unsubscribe packet has been serialized successfully.
 *      // The serialized packet is now ready to be sent to the broker.
 * }
 *
 * @endcode
 */
/* @[declare_mqtt_serializeunsubscribe] */
MQTTStatus_t MQTT_SerializeUnsubscribe( const MQTTSubscribeInfo_t * pSubscriptionList,
                                        size_t subscriptionCount,
                                        const MQTTPropBuilder_t * pUnsubscribeProperties,
                                        uint16_t packetId,
                                        uint32_t remainingLength,
                                        const MQTTFixedBuffer_t * pFixedBuffer );
/* @[declare_mqtt_serializeunsubscribe] */

/**
 * @brief Get the packet size and remaining length of an MQTT PUBLISH packet.
 *
 * #MQTT_ValidatePublishParams should be called with @p pPublishInfo before invoking this function
 * to validate the publish parameters. This function must be called before #sendPublishWithoutCopy
 * in order to get the size of the MQTT PUBLISH packet that is generated from #MQTTPublishInfo_t
 * and optional publish properties. The remaining length returned in @p pRemainingLength and the
 * packet size returned in @p pPacketSize are valid only if this function
 * returns #MQTTSuccess.
 *
 * @param[in] pPublishInfo MQTT PUBLISH packet parameters.
 * @param[in] pPublishProperties MQTT PUBLISH properties builder. Pass NULL if not used.
 * @param[out] pRemainingLength The Remaining Length of the MQTT PUBLISH packet.
 * @param[out] pPacketSize The total size of the MQTT PUBLISH packet.
 * @param[in] maxPacketSize Maximum packet size allowed by the server.
 *
 * @return #MQTTBadParameter if the packet would exceed the size allowed by the
 * MQTT spec or if invalid parameters are passed; #MQTTSuccess otherwise.
 *
 * <b>Example</b>
 * @code{c}
 *
 * // Variables used in this example.
 * MQTTStatus_t status;
 * MQTTPublishInfo_t publishInfo = { 0 };
 * MQTTPropBuilder_t publishProperties = { 0 };
 * uint16_t topicAliasMax;
 * uint8_t retainAvailable;
 * uint8_t maxQos;
 * size_t remainingLength = 0, packetSize = 0;
 *
 * // Initialize the publish info.
 * publishInfo.qos = MQTTQoS0;
 * publishInfo.pTopicName = "/some/topic/name";
 * publishInfo.topicNameLength = strlen( publishInfo.pTopicName );
 * publishInfo.pPayload = "Hello World!";
 * publishInfo.payloadLength = strlen( "Hello World!" );
 *
 * // Initialize publish properties (if needed)
 * initializePublishProperties( &publishProperties );
 *
 * // Validate publish parameters
 * status = MQTT_ValidatePublishParams(&publishInfo, topicAliasMax, retainAvailable, maxQos);
 *
 * // Get the size requirement for the publish packet.
 * status = MQTT_GetPublishPacketSize(
 *      &publishInfo,
 *      &publishProperties,
 *      &remainingLength,
 *      &packetSize,
 *      maxPacketSize
 * );
 *
 * if( status == MQTTSuccess )
 * {
 *      // The publish packet can now be sent to the broker.
 * }
 * @endcode
 */
/* @[declare_mqtt_getpublishpacketsize] */
MQTTStatus_t MQTT_GetPublishPacketSize( const MQTTPublishInfo_t * pPublishInfo,
                                        const MQTTPropBuilder_t * pPublishProperties,
                                        uint32_t * pRemainingLength,
                                        uint32_t * pPacketSize,
                                        uint32_t maxPacketSize );
/* @[declare_mqtt_getpublishpacketsize] */

/**
 * @brief Serialize an MQTT PUBLISH packet in the given buffer.
 *
 * This function will serialize complete MQTT PUBLISH packet into
 * the given buffer. If the PUBLISH payload can be sent separately,
 * consider using #MQTT_SerializePublishHeader, which will serialize
 * only the PUBLISH header into the buffer.
 *
 * #MQTT_GetPublishPacketSize should be called with @p pPublishInfo before
 * invoking this function to get the size of the required #MQTTFixedBuffer_t and
 * @p remainingLength. The @p remainingLength must be the same as returned by
 * #MQTT_GetPublishPacketSize. The #MQTTFixedBuffer_t must be at least as large
 * as the size returned by #MQTT_GetPublishPacketSize.
 *
 * @param[in] pPublishInfo MQTT PUBLISH packet parameters.
 * @param[in] pPublishProperties MQTT v5.0 properties for the PUBLISH packet. Can be NULL
 * if no properties are needed.
 * @param[in] packetId packet ID generated by #MQTT_GetPacketId.
 * @param[in] remainingLength Remaining Length provided by #MQTT_GetPublishPacketSize.
 * @param[out] pFixedBuffer Buffer for packet serialization.
 *
 * @return #MQTTNoMemory if pFixedBuffer is too small to hold the MQTT packet;
 * #MQTTBadParameter if invalid parameters are passed;
 * #MQTTSuccess otherwise.
 *
 * <b>Example</b>
 * @code{c}
 *
 * // Variables used in this example.
 * MQTTStatus_t status;
 * MQTTPublishInfo_t publishInfo = { 0 };
 * MQTTPropBuilder_t publishProperties = { 0 };
 * MQTTFixedBuffer_t fixedBuffer;
 * uint8_t buffer[ BUFFER_SIZE ];
 * size_t remainingLength = 0, packetSize = 0;
 * uint16_t packetId;
 *
 * fixedBuffer.pBuffer = buffer;
 * fixedBuffer.size = BUFFER_SIZE;
 *
 * // A packet identifier is unused for QoS 0 publishes. Otherwise, a valid, unused packet
 * // identifier must be used.
 * packetId = 0;
 *
 * // Assume publishInfo and publishProperties have been initialized. Get publish packet size.
 * status = MQTT_GetPublishPacketSize(
 *      &publishInfo, &publishProperties, &remainingLength, &packetSize
 * );
 * assert( status == MQTTSuccess );
 * assert( packetSize <= BUFFER_SIZE );
 *
 * // Serialize the publish packet into the fixed buffer.
 * status = MQTT_SerializePublish(
 *      &publishInfo,
 *      &publishProperties,
 *      packetId,
 *      remainingLength,
 *      &fixedBuffer
 * );
 *
 * if( status == MQTTSuccess )
 * {
 *      // The publish packet can now be sent to the broker.
 * }
 * @endcode
 */
/* @[declare_mqtt_serializepublish] */
MQTTStatus_t MQTT_SerializePublish( const MQTTPublishInfo_t * pPublishInfo,
                                    const MQTTPropBuilder_t * pPublishProperties,
                                    uint16_t packetId,
                                    uint32_t remainingLength,
                                    const MQTTFixedBuffer_t * pFixedBuffer );
/* @[declare_mqtt_serializepublish] */

/**
 * @brief Serialize an MQTT PUBLISH packet header without the topic string in the
 * given buffer. This function will add the topic string length to the provided
 * buffer. This helps reduce an unnecessary copy of the topic string into the
 * buffer.
 *
 * @param[in] pPublishInfo MQTT PUBLISH packet parameters.
 * @param[in] remainingLength Remaining Length provided by #MQTT_GetPublishPacketSize.
 * @param[out] pBuffer Buffer for packet serialization.
 * @param[out] headerSize Size of the serialized MQTT PUBLISH header.
 *
 * @return #MQTTSuccess if the serialization is successful. Otherwise, #MQTTBadParameter.
 */
/* @[declare_mqtt_serializepublishheaderwithouttopic] */
MQTTStatus_t MQTT_SerializePublishHeaderWithoutTopic( const MQTTPublishInfo_t * pPublishInfo,
                                                      uint32_t remainingLength,
                                                      uint8_t * pBuffer,
                                                      size_t * headerSize );
/* @[declare_mqtt_serializepublishheaderwithouttopic] */

/**
 * @brief Serialize an MQTT PUBLISH packet header in the given buffer.
 *
 * This function serializes PUBLISH header in to the given buffer. The payload
 * for PUBLISH will not be copied over to the buffer. This will help reduce
 * the memory needed for the buffer and avoid an unwanted copy operation of the
 * PUBLISH payload into the buffer. If the payload also would need to be part of
 * the serialized buffer, consider using #MQTT_SerializePublish.
 *
 * #MQTT_GetPublishPacketSize should be called with @p pPublishInfo before
 * invoking this function to get the size of the required #MQTTFixedBuffer_t and
 * @p remainingLength. The @p remainingLength must be the same as returned by
 * #MQTT_GetPublishPacketSize. The #MQTTFixedBuffer_t must be at least as large
 * as the size returned by #MQTT_GetPublishPacketSize.
 *
 * @param[in] pPublishInfo MQTT PUBLISH packet parameters.
 * @param[in] pPublishProperties MQTT v5.0 properties for the PUBLISH packet. Can be NULL
 * if no properties are needed.
 * @param[in] packetId packet ID generated by #MQTT_GetPacketId.
 * @param[in] remainingLength Remaining Length provided by #MQTT_GetPublishPacketSize.
 * @param[out] pFixedBuffer Buffer for packet serialization.
 * @param[out] pHeaderSize Size of the serialized MQTT PUBLISH header.
 *
 * @return #MQTTNoMemory if pFixedBuffer is too small to hold the MQTT packet;
 * #MQTTBadParameter if invalid parameters are passed;
 * #MQTTSuccess otherwise.
 *
 * <b>Example</b>
 * @code{c}
 *
 * // Variables used in this example.
 * MQTTStatus_t status;
 * MQTTPublishInfo_t publishInfo = { 0 };
 * MQTTPropBuilder_t publishProperties ;
 * MQTTFixedBuffer_t fixedBuffer;
 * uint8_t buffer[ BUFFER_SIZE ];
 * size_t remainingLength = 0, packetSize = 0, headerSize = 0;
 * uint16_t packetId;
 * int32_t bytesSent;
 * uint32_t maxPacketSize = pContext->connectionProperties.serverMaxPacketSize;
 *
 * fixedBuffer.pBuffer = buffer;
 * fixedBuffer.size = BUFFER_SIZE;
 *
 * // A packet identifier is unused for QoS 0 publishes. Otherwise, a valid, unused packet
 * // identifier must be used.
 * packetId = 0;
 *
 * // Assume publishInfo and publishProperties have been initialized. Get the publish packet size.
 * status = MQTT_GetPublishPacketSize(
 *      &publishInfo, &publishProperties, &remainingLength, &packetSize, maxPacketSize );
 * assert( status == MQTTSuccess );
 * // The payload will not be serialized, so the the fixed buffer does not need to hold it.
 * assert( ( packetSize - publishInfo.payloadLength ) <= BUFFER_SIZE );
 *
 * // Serialize the publish packet header into the fixed buffer.
 * status = MQTT_SerializePublishHeader(
 *      &publishInfo,
 *      &publishProperties,
 *      packetId,
 *      remainingLength,
 *      &fixedBuffer,
 *      &headerSize
 * );
 *
 * if( status == MQTTSuccess )
 * {
 *      // The publish header and payload can now be sent to the broker.
 *      // mqttSocket here is a socket descriptor created and connected to the MQTT
 *      // broker outside of this function.
 *      bytesSent = send( mqttSocket, ( void * ) fixedBuffer.pBuffer, headerSize, 0 );
 *      assert( bytesSent == headerSize );
 *      bytesSent = send( mqttSocket, publishInfo.pPayload, publishInfo.payloadLength, 0 );
 *      assert( bytesSent == publishInfo.payloadLength );
 * }
 * @endcode
 */
/* @[declare_mqtt_serializepublishheader] */
MQTTStatus_t MQTT_SerializePublishHeader( const MQTTPublishInfo_t * pPublishInfo,
                                          const MQTTPropBuilder_t * pPublishProperties,
                                          uint16_t packetId,
                                          uint32_t remainingLength,
                                          const MQTTFixedBuffer_t * pFixedBuffer,
                                          size_t * pHeaderSize );
/* @[declare_mqtt_serializepublishheader] */

/**
 * @brief Serialize an MQTT PUBACK, PUBREC, PUBREL, or PUBCOMP into the given
 * buffer.
 *
 * @param[out] pFixedBuffer Buffer for packet serialization.
 * @param[in] packetType Byte of the corresponding packet fixed header per the
 * MQTT spec.
 * @param[in] packetId Packet ID of the publish.
 * @param[in] pAckProperties Optional properties to be added to the ACK packet.
 * @param[in] pReasonCode Optional reason code to be added to the ACK packet.
 *
 * @note If any properties are provided to the function to be added to the ack
 * packet, then a reason code must be provided as well.
 *
 * @return #MQTTBadParameter, #MQTTNoMemory, or #MQTTSuccess.
 *
 * <b>Example</b>
 * @code{c}
 *
 * // Variables used in this example.
 * MQTTStatus_t status;
 * MQTTFixedBuffer_t fixedBuffer;
 * uint8_t buffer[ BUFFER_SIZE ];
 * uint16_t packetId;
 * uint8_t packetType;
 *
 * fixedBuffer.pBuffer = buffer;
 * fixedBuffer.size = BUFFER_SIZE;
 * // The fixed buffer must be large enough to hold 4 bytes.
 * assert( BUFFER_SIZE >= MQTT_PUBLISH_ACK_PACKET_SIZE );
 *
 * // The packet ID must be the same as the original publish packet.
 * packetId = publishPacketId;
 *
 * // The byte representing a packet of type ACK. This function accepts PUBACK, PUBREC, PUBREL, or PUBCOMP.
 * packetType = MQTT_PACKET_TYPE_PUBACK;
 *
 * // Serialize the publish acknowledgment into the fixed buffer without any properties or reason code.
 * status = MQTT_SerializeAck( &fixedBuffer, packetType, packetId, NULL, NULL );
 *
 * if( status == MQTTSuccess )
 * {
 *      // The publish acknowledgment can now be sent to the broker.
 * }
 * @endcode
 */
/* @[declare_mqtt_serializeack] */
MQTTStatus_t MQTT_SerializeAck( const MQTTFixedBuffer_t * pFixedBuffer,
                                uint8_t packetType,
                                uint16_t packetId,
                                const MQTTPropBuilder_t * pAckProperties,
                                const MQTTSuccessFailReasonCode_t * pReasonCode );
/* @[declare_mqtt_serializeack] */

/**
 * @brief Get the size of an MQTT DISCONNECT packet.
 *
 * @param[in] pDisconnectProperties MQTT DISCONNECT properties builder. Pass NULL if
 *                     not used.
 * @param[out] pRemainingLength The Remaining Length of the MQTT DISCONNECT packet.
 * @param[out] pPacketSize The size of the MQTT DISCONNECT packet.
 * @param[in] maxPacketSize Maximum packet size allowed by the server.
 * @param[in] pReasonCode The reason code for the disconnect. Pass NULL if not used -
 *                     only valid if the properties are NULL too.
 *
 * @return #MQTTSuccess, or #MQTTBadParameter if parameters are invalid
 *
 * <b>Example</b>
 * @code{c}
 *
 * // Variables used in this example.
 * MQTTStatus_t status;
 * uint32_t remainingLength = 0;
 * uint32_t packetSize = 0;
 * uint32_t maxPacketSize;
 * MQTTPropBuilder_t disconnectProperties ;
 * MQTTSuccessFailReasonCode_t reasonCode = MQTT_REASON_DISCONNECT_NORMAL_DISCONNECTION;
 *
 * //Set property builder. The details are out of scope for this example.
 * initializePropertyBuilder( &disconnectProperties );
 *
 * //Set the parameters.
 * // Get the size requirement for the disconnect packet.
 * status = MQTT_GetDisconnectPacketSize( &disconnectProperties, &remainingLength, &packetSize, maxPacketSize, &reasonCode );
 *
 * if( status == MQTTSuccess )
 * {
 *      // Send the disconnect packet.
 * }
 * @endcode
 */
/* @[declare_mqtt_getdisconnectpacketsize] */
MQTTStatus_t MQTT_GetDisconnectPacketSize( const MQTTPropBuilder_t * pDisconnectProperties,
                                           uint32_t * pRemainingLength,
                                           uint32_t * pPacketSize,
                                           uint32_t maxPacketSize,
                                           const MQTTSuccessFailReasonCode_t * pReasonCode );
/* @[declare_mqtt_getdisconnectpacketsize] */

/**
 * @brief Serialize an MQTT DISCONNECT packet into the given buffer.
 *
 * The input #MQTTFixedBuffer_t.size must be at least as large as the size
 * returned by #MQTT_GetDisconnectPacketSize. This function should only be called
 * after #MQTT_GetDisconnectPacketSize to ensure proper buffer sizing.
 *
 * @param[in] pDisconnectProperties MQTT v5.0 properties for the DISCONNECT packet. Can be NULL
 * if no properties are needed.
 * @param[in] pReasonCode The reason code for the disconnect. For MQTT v5.0, this indicates
 * why the connection is being terminated. If this is NULL, then the pDisconnectProperties must
 * be NULL as well.
 * @param[in] remainingLength Remaining Length provided by #MQTT_GetDisconnectPacketSize.
 * @param[out] pFixedBuffer Buffer for packet serialization.
 *
 * @return #MQTTNoMemory if pFixedBuffer is too small to hold the MQTT packet;
 * #MQTTBadParameter if invalid parameters are passed;
 * #MQTTSuccess otherwise.
 *
 * <b>Example</b>
 * @code{c}
 *
 * // Variables used in this example.
 * MQTTStatus_t status;
 * MQTTFixedBuffer_t fixedBuffer;
 * MQTTPropBuilder_t disconnectProperties = { 0 };
 * uint8_t buffer[ BUFFER_SIZE ];
 * uint32_t remainingLength = 0, packetSize = 0;
 *
 * fixedBuffer.pBuffer = buffer;
 * fixedBuffer.size = BUFFER_SIZE;
 *
 * MQTTSuccessFailReasonCode_t reasonCode = MQTT_REASON_DISCONNECT_NORMAL_DISCONNECTION;
 * // Get the disconnect packet size.
 * status = MQTT_GetDisconnectPacketSize( &disconnectProperties,
 *                                        &remainingLength,
 *                                        &packetSize,
 *                                        MQTT_MAX_REMAINING_LENGTH,
 *                                        &reasonCode );
 * assert( status == MQTTSuccess );
 * assert( packetSize <= BUFFER_SIZE );
 *
 * // Serialize the disconnect into the fixed buffer.
 * status = MQTT_SerializeDisconnect( &disconnectProperties,
 *                                   &reasonCode,
 *                                   remainingLength,
 *                                   &fixedBuffer );
 *
 * if( status == MQTTSuccess )
 * {
 *      // The disconnect packet can now be sent to the broker.
 * }
 * @endcode
 */
/* @[declare_mqtt_serializedisconnect] */
MQTTStatus_t MQTT_SerializeDisconnect( const MQTTPropBuilder_t * pDisconnectProperties,
                                       const MQTTSuccessFailReasonCode_t * pReasonCode,
                                       uint32_t remainingLength,
                                       const MQTTFixedBuffer_t * pFixedBuffer );
/* @[declare_mqtt_serializedisconnect] */

/**
 * @brief Get the size of an MQTT PINGREQ packet.
 *
 * @param[out] pPacketSize The size of the MQTT PINGREQ packet.
 *
 * @return  #MQTTSuccess or #MQTTBadParameter if pPacketSize is NULL.
 *
 * <b>Example</b>
 * @code{c}
 *
 * // Variables used in this example.
 * MQTTStatus_t status;
 * uint32_t packetSize = 0;
 *
 * // Get the size requirement for the ping request packet.
 * status = MQTT_GetPingreqPacketSize( &packetSize );
 * assert( status == MQTTSuccess );
 * assert( packetSize == 2 );
 *
 * // The application should allocate or use a static #MQTTFixedBuffer_t of
 * // size >= 2 to serialize the ping request.
 *
 * @endcode
 */
/* @[declare_mqtt_getpingreqpacketsize] */
MQTTStatus_t MQTT_GetPingreqPacketSize( uint32_t * pPacketSize );
/* @[declare_mqtt_getpingreqpacketsize] */

/**
 * @brief Serialize an MQTT PINGREQ packet into the given buffer.
 *
 * The input #MQTTFixedBuffer_t.size must be at least as large as the size
 * returned by #MQTT_GetPingreqPacketSize.
 *
 * @param[out] pFixedBuffer Buffer for packet serialization.
 *
 * @return #MQTTNoMemory if pFixedBuffer is too small to hold the MQTT packet;
 * #MQTTBadParameter if invalid parameters are passed;
 * #MQTTSuccess otherwise.
 *
 * <b>Example</b>
 * @code{c}
 *
 * // Variables used in this example.
 * MQTTStatus_t status;
 * MQTTFixedBuffer_t fixedBuffer;
 * uint8_t buffer[ BUFFER_SIZE ];
 *
 * fixedBuffer.pBuffer = buffer;
 * fixedBuffer.size = BUFFER_SIZE;
 *
 * // Get the ping request packet size.
 * status = MQTT_GetPingreqPacketSize( &packetSize );
 * assert( status == MQTTSuccess );
 * assert( packetSize <= BUFFER_SIZE );
 *
 * // Serialize the ping request into the fixed buffer.
 * status = MQTT_SerializePingreq( &fixedBuffer );
 *
 * if( status == MQTTSuccess )
 * {
 *      // The ping request can now be sent to the broker.
 * }
 * @endcode
 */
/* @[declare_mqtt_serializepingreq] */
MQTTStatus_t MQTT_SerializePingreq( const MQTTFixedBuffer_t * pFixedBuffer );
/* @[declare_mqtt_serializepingreq] */

/**
 * @brief Deserialize an MQTT PUBLISH packet.
 *
 * @param[in] pIncomingPacket #MQTTPacketInfo_t containing the buffer.
 * @param[out] pPacketId The packet ID obtained from the buffer.
 * @param[out] pPublishInfo Struct containing information about the publish.
 * @param[in] propBuffer Buffer to hold the properties.
 * @param[in] maxPacketSize Maximum packet size.
 * @param[in] topicAliasMax Maximum topic alias specified in the CONNECT packet.
 *
 * @return
 * - #MQTTBadParameter if invalid parameters are passed
 * - #MQTTBadResponse if invalid packet is read
 * - #MQTTSuccess otherwise.
 *
 * <b>Example</b>
 * @code{c}
 *
 * // TransportRecv_t function for reading from the network.
 * int32_t socket_recv(
 *      NetworkContext_t * pNetworkContext,
 *      void * pBuffer,
 *      size_t bytesToRecv
 * );
 * // Some context to be used with the above transport receive function.
 * NetworkContext_t networkContext;
 *
 * // Other variables used in this example.
 * MQTTStatus_t status;
 * MQTTPacketInfo_t incomingPacket;
 * MQTTPublishInfo_t publishInfo = { 0 };
 * MQTTPropBuilder_t propBuffer ;
 * uint16_t packetId;
 * uint32_t maxPacketSize = pContext->connectionProperties.maxPacketSize;
 * uint16_t topicAliasMax = pContext->connectionProperties.topicAliasMax;
 *
 * int32_t bytesRecvd;
 * // A buffer to hold remaining data of the incoming packet.
 * uint8_t buffer[ BUFFER_SIZE ];
 *
 * // Populate all fields of the incoming packet.
 * status = MQTT_GetIncomingPacketTypeAndLength(
 *      socket_recv,
 *      &networkContext,
 *      &incomingPacket
 * );
 * assert( status == MQTTSuccess );
 * assert( incomingPacket.remainingLength <= BUFFER_SIZE );
 * bytesRecvd = socket_recv(
 *      &networkContext,
 *      ( void * ) buffer,
 *      incomingPacket.remainingLength
 * );
 * incomingPacket.pRemainingData = buffer;
 *
 * // Deserialize the publish information if the incoming packet is a publish.
 * if( ( incomingPacket.type & 0xF0 ) == MQTT_PACKET_TYPE_PUBLISH )
 * {
 *      status = MQTT_DeserializePublish( &incomingPacket, &packetId, &publishInfo,
 *                                        &propBuffer, maxPacketSize, topicAliasMax );
 *      if( status == MQTTSuccess )
 *      {
 *          // The deserialized publish information can now be used from `publishInfo`.
 *      }
 * }
 * @endcode
 */
/* @[declare_mqtt_deserializepublish] */
MQTTStatus_t MQTT_DeserializePublish( const MQTTPacketInfo_t * pIncomingPacket,
                                      uint16_t * pPacketId,
                                      MQTTPublishInfo_t * pPublishInfo,
                                      MQTTPropBuilder_t * propBuffer,
                                      uint32_t maxPacketSize,
                                      uint16_t topicAliasMax );
/* @[declare_mqtt_deserializepublish] */

/**
 * @brief Deserialize an MQTT PUBACK, PUBREC, PUBREL, PUBCOMP, SUBACK, UNSUBACK, or PINGRESP.
 *
 * @param[in] pIncomingPacket #MQTTPacketInfo_t containing the buffer.
 * @param[out] pPacketId The packet ID obtained from the buffer.
 * @param[out] pReasonCode Struct to store reason code(s) from the acknowledgment packet.
 *                        Contains the success/failure status of the corresponding request.
 * @param[out] pPropBuffer Struct to store the deserialized acknowledgment properties.
 *                       Will contain any MQTT v5.0 properties included in the ack packet.
 * @param[in,out] pConnectProperties Struct to store the deserialized connect/connack properties.
 *
 * @return Returns one of the following:
 * - #MQTTSuccess if the packet was successfully deserialized
 * - #MQTTBadParameter if invalid parameters are passed
 * - #MQTTBadResponse if the packet type is invalid or packet parsing fails
 *
 * <b>Example</b>
 * @code{c}
 *
 * // Variables used in this example.
 * MQTTStatus_t status;
 * MQTTPacketInfo_t incomingPacket;
 * uint16_t packetId;
 * MQTTReasonCodeInfo_t reasonCode ; // Can be set to NULL if the incoming packet is CONNACK or PINGRESP
 * MQTTPropBuilder_t propBuffer; // Can be set to NULL if the user does not want any incoming properties.
 * MQTTConnectionProperties_t connectionProperties = pContext->connectionProperties;  // Cannot be set to NULL.
 *
 * // Receive an incoming packet and populate all fields. The details are out of scope
 * // for this example.
 * receiveIncomingPacket(&incomingPacket);
 *
 * // Deserialize ack information if the incoming packet is a publish ack.
 * status = MQTT_DeserializeAck( &incomingPacket,
 *                               &packetId,
 *                               &reasonCode,
 *                               &propBuffer,
 *                               &connectionProperties );
 * if(status == MQTTSuccess)
 * {
 *     // Ack information is now available.
 * }
 * @endcode
 */
/* @[declare_mqtt_deserializeack] */
MQTTStatus_t MQTT_DeserializeAck( const MQTTPacketInfo_t * pIncomingPacket,
                                  uint16_t * pPacketId,
                                  MQTTReasonCodeInfo_t * pReasonCode,
                                  MQTTPropBuilder_t * pPropBuffer,
                                  const MQTTConnectionProperties_t * pConnectProperties );
/* @[declare_mqtt_deserializeack] */

/**
 * @brief Deserialize an MQTT CONNACK.
 *
 * @param[in] pIncomingPacket #MQTTPacketInfo_t containing the buffer.
 * @param[out] pSessionPresent Boolean flag from a CONNACK indicating present session.
 * @param[out] pPropBuffer Struct to store the deserialized acknowledgment properties.
 *                       Will contain any MQTT v5.0 properties included in the ack packet.
 * @param[in,out] pConnectProperties Struct to store the deserialized connect/connack properties.
 *                                   This parameter cannot be NULL.
 *
 * @return #MQTTBadParameter, #MQTTBadResponse, #MQTTServerRefused, or #MQTTSuccess.
 */
/* @[declare_mqtt_deserializeconnack] */
MQTTStatus_t MQTT_DeserializeConnAck( const MQTTPacketInfo_t * pIncomingPacket,
                                      bool * pSessionPresent,
                                      MQTTPropBuilder_t * pPropBuffer,
                                      MQTTConnectionProperties_t * pConnectProperties );
/* @[declare_mqtt_deserializeconnack] */

/**
 * @brief Extract the MQTT packet type and length from incoming packet.
 *
 * This function must be called for every incoming packet to retrieve the
 * #MQTTPacketInfo_t.type and #MQTTPacketInfo_t.remainingLength. A
 * #MQTTPacketInfo_t is not valid until this routine has been invoked.
 *
 * @param[in] readFunc Transport layer read function pointer.
 * @param[in] pNetworkContext The network context pointer provided by the application.
 * @param[out] pIncomingPacket Pointer to MQTTPacketInfo_t structure. This is
 * where type, remaining length and packet identifier are stored.
 *
 * @return #MQTTSuccess on successful extraction of type and length,
 * #MQTTBadParameter if @p pIncomingPacket is invalid,
 * #MQTTRecvFailed on transport receive failure,
 * #MQTTBadResponse if an invalid packet is read, and
 * #MQTTNoDataAvailable if there is nothing to read.
 *
 * <b>Example</b>
 * @code{c}
 *
 * // TransportRecv_t function for reading from the network.
 * int32_t socket_recv(
 *      NetworkContext_t * pNetworkContext,
 *      void * pBuffer,
 *      size_t bytesToRecv
 * );
 * // Some context to be used with above transport receive function.
 * NetworkContext_t networkContext;
 *
 * // Struct to hold the incoming packet information.
 * MQTTPacketInfo_t incomingPacket;
 * MQTTStatus_t status = MQTTSuccess;
 * int32_t bytesRecvd;
 * // Buffer to hold the remaining data of the incoming packet.
 * uint8_t buffer[ BUFFER_SIZE ];
 *
 * // Loop until data is available to be received.
 * do{
 *      status = MQTT_GetIncomingPacketTypeAndLength(
 *          socket_recv,
 *          &networkContext,
 *          &incomingPacket
 *      );
 * } while( status == MQTTNoDataAvailable );
 *
 * assert( status == MQTTSuccess );
 *
 * // Receive the rest of the incoming packet.
 * assert( incomingPacket.remainingLength <= BUFFER_SIZE );
 * bytesRecvd = socket_recv(
 *      &networkContext,
 *      ( void * ) buffer,
 *      incomingPacket.remainingLength
 * );
 *
 * // Set the remaining data field.
 * incomingPacket.pRemainingData = buffer;
 * @endcode
 */
/* @[declare_mqtt_getincomingpackettypeandlength] */
MQTTStatus_t MQTT_GetIncomingPacketTypeAndLength( TransportRecv_t readFunc,
                                                  NetworkContext_t * pNetworkContext,
                                                  MQTTPacketInfo_t * pIncomingPacket );
/* @[declare_mqtt_getincomingpackettypeandlength] */

/**
 * @brief Extract the MQTT packet type and length from incoming packet.
 *
 * This function must be called for every incoming packet to retrieve the
 * #MQTTPacketInfo_t.type and #MQTTPacketInfo_t.remainingLength. A
 * #MQTTPacketInfo_t is not valid until this routine has been invoked.
 *
 * @param[in] pBuffer The buffer holding the raw data to be processed
 * @param[in] pIndex Pointer to the index within the buffer to marking the end
 *            of raw data available.
 * @param[out] pIncomingPacket Structure used to hold the fields of the
 *            incoming packet.
 *
 * @return #MQTTSuccess on successful extraction of type and length,
 * #MQTTBadParameter if @p pIncomingPacket is invalid,
 * #MQTTBadResponse if an invalid packet is read, and
 * #MQTTNoDataAvailable if there is nothing to read.
 */
 /* @[declare_mqtt_processincomingpackettypeandlength] */
MQTTStatus_t MQTT_ProcessIncomingPacketTypeAndLength( const uint8_t * pBuffer,
                                                      const size_t * pIndex,
                                                      MQTTPacketInfo_t * pIncomingPacket );
/* @[declare_mqtt_processincomingpackettypeandlength] */

/**
 * @brief Update the duplicate publish flag within the given header of the publish packet.
 *
 * @param[in] pHeader The buffer holding the header content
 * @param[in] set If true then the flag will be set else cleared
 *
 * @return #MQTTSuccess on successful setting of the duplicate flag,
 * #MQTTBadParameter for invalid parameters
 */
 /* @[declare_mqtt_updateduplicatepublishflag] */
MQTTStatus_t MQTT_UpdateDuplicatePublishFlag( uint8_t * pHeader, bool set );
/* @[declare_mqtt_updateduplicatepublishflag] */

/**
 * @brief Initialize an MQTTConnectionProperties_t.
 *
 * @note This function initializes the connect properties to default values.
 *       This function should only be used if using only serializer functions
 *       throughout the connection. It is also important to only call this function
 *       before sending the connect packet.
 *
 * @param[in] pConnectProperties The connect properties to initialize.
 *
 * @return
 * - #MQTTBadParameter if pConnectProperties is NULL.
 * - #MQTTSuccess otherwise.
 */
/* @[declare_mqtt_initconnect] */
MQTTStatus_t MQTT_InitConnect( MQTTConnectionProperties_t * pConnectProperties );
/* @[declare_mqtt_initconnect] */

/**
 * @brief Initialize the property builder.
 *
 * @param[out] pPropertyBuilder Property builder to initialize.
 * @param[in] buffer Buffer to store the properties.
 * @param[in] length Length of the buffer.
 *
 * @return
 * - #MQTTBadParameter if invalid parameters are passed.
 * - #MQTTSuccess otherwise.
 */
/* @[declare_mqttpropertybuilder_init] */
MQTTStatus_t MQTTPropertyBuilder_Init( MQTTPropBuilder_t * pPropertyBuilder,
                                       uint8_t * buffer,
                                       size_t length );
/* @[declare_mqttpropertybuilder_init] */

/**
 * @brief Validates the properties specified for WILL Properties in the MQTT CONNECT packet.
 *
 * @param[in] pPropertyBuilder Pointer to the property builder structure containing will properties.
 *
 * @return Returns one of the following:
 * - #MQTTSuccess , #MQTTBadParameter or #MQTTBadResponse.
 */
/* @[declare_mqtt_validatewillproperties] */
MQTTStatus_t MQTT_ValidateWillProperties( const MQTTPropBuilder_t * pPropertyBuilder );
/* @[declare_mqtt_validatewillproperties] */


 /**
 * @brief Validate the properties in a CONNECT packet.
 *
 * @param[in] pPropertyBuilder Pointer to the property builder structure containing connect packet
 * properties.
 * @param[out] isRequestProblemInfoSet Whether the request problem info field is set in the properties.
 * @param[out] pPacketMaxSizeValue Optional pointer to get the Maximum Packet Size from the properties.
 * If not required, NULL can be passed.
 *
 * @return Returns one of the following:
 * - #MQTTSuccess , #MQTTBadParameter or #MQTTBadResponse.
 */
/* @[declare_mqtt_validateconnectproperties] */
MQTTStatus_t MQTT_ValidateConnectProperties( const MQTTPropBuilder_t * pPropertyBuilder,
                                             bool * isRequestProblemInfoSet,
                                             uint32_t * pPacketMaxSizeValue );
/* @[declare_mqtt_validateconnectproperties] */

/**
 * @brief Adds a Subscription Identifier property to the MQTT property builder.
 *
 * This function adds a Subscription Identifier property to the property builder.
 *
 * @param[out] pPropertyBuilder   Pointer to the property builder structure where
 *                                the Subscription Identifier will be added.
 *                                Must not be NULL.
 * @param[in] subscriptionId The Subscription Identifier value to be added.
 *                          Must be greater than 0.
 * @param[in]  pOptionalMqttPacketType Optional MQTT packet type for which the property
 *            is being added. The function will check whether the given property can be
 *            added to the packet type if it is provided.
 *
 * @return Returns one of the following:
 * - #MQTTSuccess if the Subscription Identifier was successfully added
 * - #MQTTBadParameter if pPropertyBuilder is NULL or subscriptionId is 0
 * - #MQTTNoMemory if the property builder has insufficient space
 *
 * <b>Example</b>
 * @code{c}
 * // Variables used in this example.
 * MQTTStatus_t status;
 * MQTTPropBuilder_t propertyBuilder ; // Assume this is initialized properly
 * uint32_t subscriptionId = 12345;
 *
 * // Add Subscription Identifier to property builder
 * status = MQTTPropAdd_SubscriptionId(&propertyBuilder, subscriptionId, MQTT_PROP_VALIDATE_SUBSCRIBE);
 *
 * if(status == MQTTSuccess)
 * {
 *     // Subscription Identifier successfully added
 * }
 * @endcode
 *
 * @note This property is only valid for MQTT v5.0 and above.
 * @note The Subscription Identifier can be used in SUBSCRIBE packets and
 *       will be returned in matched PUBLISH packets.
 */

/* @[declare_mqttpropadd_subscriptionid] */
MQTTStatus_t MQTTPropAdd_SubscriptionId( MQTTPropBuilder_t * pPropertyBuilder,
                                         uint32_t subscriptionId,
                                         const uint8_t * pOptionalMqttPacketType );
/* @[declare_mqttpropadd_subscriptionid] */

/**
 * @brief Adds User Property to the MQTT property builder.
 *
 * This function adds User Property to the property builder.
 *
 * @param[out] pPropertyBuilder   Pointer to the property builder structure.
 * @param[in]  userProperty       The User Property to be added.
 * @param[in]  pOptionalMqttPacketType Optional MQTT packet type for which the property
 *            is being added. The function will check whether the given property can be
 *            added to the packet type if it is provided.
 *
 * @return Returns one of the following:
 * - #MQTTSuccess if the Subscription Identifier was successfully added
 * - #MQTTBadParameter if an invalid parameter is passed
 * - #MQTTNoMemory if the property builder has insufficient space
 */
/* @[declare_mqttpropadd_userprop] */
MQTTStatus_t MQTTPropAdd_UserProp( MQTTPropBuilder_t * pPropertyBuilder,
                                   const MQTTUserProperty_t * userProperty,
                                   const uint8_t * pOptionalMqttPacketType );
/* @[declare_mqttpropadd_userprop] */

/**
 * @brief Adds Session Expiry Interval property to the MQTT property builder.
 *
 * This function adds Session Expiry Interval property to the property builder.
 *
 * @param[out] pPropertyBuilder   Pointer to the property builder structure.
 * @param[in]  sessionExpiry     The Session Expiry Interval in seconds.
 * @param[in]  pOptionalMqttPacketType Optional MQTT packet type for validation.
 *                                     Can be NULL to skip packet type validation.
 *
 * @return Returns one of the following:
 * - #MQTTSuccess if the Session Expiry Interval was successfully added
 * - #MQTTBadParameter if an invalid parameter is passed
 * - #MQTTNoMemory if the property builder has insufficient space
 */
/* @[declare_mqttpropadd_sessionexpiry] */
MQTTStatus_t MQTTPropAdd_SessionExpiry( MQTTPropBuilder_t * pPropertyBuilder,
                                        uint32_t sessionExpiry,
                                        const uint8_t * pOptionalMqttPacketType );
/* @[declare_mqttpropadd_sessionexpiry] */

/**
 * @brief Adds Receive Maximum property to the MQTT property builder.
 *
 * This function adds Receive Maximum property to the property builder.
 *
 * @param[out] pPropertyBuilder   Pointer to the property builder structure.
 * @param[in] receiveMax The maximum number of QoS 1 and QoS 2 messages allowed to be
 *             received simultaneously.
 * @param[in] pOptionalMqttPacketType Optional MQTT packet type for which the property
 *            is being added. The function will check whether the given property can be
 *            added to the packet type if it is provided.
 *
 * @return Returns one of the following:
 * - #MQTTSuccess if the Receive Maximum was successfully added
 * - #MQTTBadParameter if an invalid parameter is passed
 * - #MQTTNoMemory if the property builder has insufficient space
 */
/* @[declare_mqttpropadd_receivemax] */
MQTTStatus_t MQTTPropAdd_ReceiveMax( MQTTPropBuilder_t * pPropertyBuilder,
                                     uint16_t receiveMax,
                                     const uint8_t * pOptionalMqttPacketType );
/* @[declare_mqttpropadd_receivemax] */

/**
 * @brief Adds Maximum Packet Size property to the MQTT property builder.
 *
 * This function adds Maximum Packet Size property to the property builder.
 *
 * @param[out] pPropertyBuilder   Pointer to the property builder structure.
 * @param[in]  maxPacketSize     The maximum packet size the client is willing to accept.
 * @param[in]  pOptionalMqttPacketType Optional MQTT packet type for which the property
 *            is being added. The function will check whether the given property can be
 *            added to the packet type if it is provided.
 *
 * @return Returns one of the following:
 * - #MQTTSuccess if the Maximum Packet Size was successfully added
 * - #MQTTBadParameter if an invalid parameter is passed
 * - #MQTTNoMemory if the property builder has insufficient space
 */
/* @[declare_mqttpropadd_maxpacketsize] */
MQTTStatus_t MQTTPropAdd_MaxPacketSize( MQTTPropBuilder_t * pPropertyBuilder,
                                        uint32_t maxPacketSize,
                                        const uint8_t * pOptionalMqttPacketType );
/* @[declare_mqttpropadd_maxpacketsize] */

/**
 * @brief Adds Topic Alias Maximum property to the MQTT property builder.
 *
 * This function adds Topic Alias Maximum property to the property builder.
 *
 * @param[out] pPropertyBuilder   Pointer to the property builder structure.
 * @param[in]  topicAliasMax     The maximum value of topic alias accepted by the client.
 * @param[in]  pOptionalMqttPacketType Optional MQTT packet type for which the property
 *            is being added. The function will check whether the given property can be
 *            added to the packet type if it is provided.
 *
 * @return Returns one of the following:
 * - #MQTTSuccess if the Topic Alias Maximum was successfully added
 * - #MQTTBadParameter if an invalid parameter is passed
 * - #MQTTNoMemory if the property builder has insufficient space
 */
/* @[declare_mqttpropadd_topicaliasmax] */
MQTTStatus_t MQTTPropAdd_TopicAliasMax( MQTTPropBuilder_t * pPropertyBuilder,
                                        uint16_t topicAliasMax,
                                        const uint8_t * pOptionalMqttPacketType );
/* @[declare_mqttpropadd_topicaliasmax] */

/**
 * @brief Adds Request Response Information property to the MQTT property builder.
 *
 * This function adds Request Response Information property to the property builder.
 *
 * @param[out] pPropertyBuilder       Pointer to the property builder structure.
 * @param[in]  requestResponseInfo    Boolean indicating whether response information is requested.
 * @param[in]  pOptionalMqttPacketType Optional MQTT packet type for which the property
 *            is being added. The function will check whether the given property can be
 *            added to the packet type if it is provided.
 *
 * @return Returns one of the following:
 * - #MQTTSuccess if the Request Response Information was successfully added
 * - #MQTTBadParameter if an invalid parameter is passed
 * - #MQTTNoMemory if the property builder has insufficient space
 */
/* @[declare_mqttpropadd_requestrespinfo] */
MQTTStatus_t MQTTPropAdd_RequestRespInfo( MQTTPropBuilder_t * pPropertyBuilder,
                                          bool requestResponseInfo,
                                          const uint8_t * pOptionalMqttPacketType );
/* @[declare_mqttpropadd_requestrespinfo] */

/**
 * @brief Adds Request Problem Information property to the MQTT property builder.
 *
 * This function adds Request Problem Information property to the property builder.
 *
 * @param[out] pPropertyBuilder       Pointer to the property builder structure.
 * @param[in]  requestProblemInfo    Boolean indicating whether problem information is requested.
 * @param[in]  pOptionalMqttPacketType Optional MQTT packet type for which the property
 *            is being added. The function will check whether the given property can be
 *            added to the packet type if it is provided.
 *
 * @return Returns one of the following:
 * - #MQTTSuccess if the Request Problem Information was successfully added
 * - #MQTTBadParameter if an invalid parameter is passed
 * - #MQTTNoMemory if the property builder has insufficient space
 */
/* @[declare_mqttpropadd_requestprobinfo] */
MQTTStatus_t MQTTPropAdd_RequestProbInfo( MQTTPropBuilder_t * pPropertyBuilder,
                                          bool requestProblemInfo,
                                          const uint8_t * pOptionalMqttPacketType );
/* @[declare_mqttpropadd_requestprobinfo] */

/**
 * @brief Adds Authentication Method property to the MQTT property builder.
 *
 * This function adds Authentication Method property to the property builder.
 *
 * @param[out] pPropertyBuilder   Pointer to the property builder structure.
 * @param[in]  authMethod        Pointer to the authentication method string.
 * @param[in]  authMethodLength  Length of the authentication method string (must be less than 65536).
 * @param[in]  pOptionalMqttPacketType Optional MQTT packet type for which the property
 *            is being added. The function will check whether the given property can be
 *            added to the packet type if it is provided.
 *
 * @return Returns one of the following:
 * - #MQTTSuccess if the Authentication Method was successfully added
 * - #MQTTBadParameter if an invalid parameter is passed
 * - #MQTTNoMemory if the property builder has insufficient space
 */
/* @[declare_mqttpropadd_authmethod] */
MQTTStatus_t MQTTPropAdd_AuthMethod( MQTTPropBuilder_t * pPropertyBuilder,
                                     const char * authMethod,
                                     size_t authMethodLength,
                                     const uint8_t * pOptionalMqttPacketType );
/* @[declare_mqttpropadd_authmethod] */

/**
 * @brief Adds Authentication Data property to the MQTT property builder.
 *
 * This function adds Authentication Data property to the property builder.
 *
 * @param[out] pPropertyBuilder   Pointer to the property builder structure.
 * @param[in]  authData          Pointer to the authentication data.
 * @param[in]  authDataLength    Length of the authentication data (must be less than 65536).
 * @param[in]  pOptionalMqttPacketType Optional MQTT packet type for which the property
 *            is being added. The function will check whether the given property can be
 *            added to the packet type if it is provided.
 *
 * @return Returns one of the following:
 * - #MQTTSuccess if the Authentication Data was successfully added
 * - #MQTTBadParameter if an invalid parameter is passed
 * - #MQTTNoMemory if the property builder has insufficient space
 */
/* @[declare_mqttpropadd_authdata] */
MQTTStatus_t MQTTPropAdd_AuthData( MQTTPropBuilder_t * pPropertyBuilder,
                                   const char * authData,
                                   size_t authDataLength,
                                   const uint8_t * pOptionalMqttPacketType );
/* @[declare_mqttpropadd_authdata] */

/**
 * @brief Adds Payload Format Indicator property to the MQTT property builder.
 *
 * This function adds Payload Format Indicator property to the property builder.
 *
 * @param[out] pPropertyBuilder   Pointer to the property builder structure.
 * @param[in]  payloadFormat     Boolean indicating the payload format (true for UTF-8, false for unspecified bytes).
 * @param[in]  pOptionalMqttPacketType Optional MQTT packet type for which the property
 *            is being added. The function will check whether the given property can be
 *            added to the packet type if it is provided.
 *
 * @return Returns one of the following:
 * - #MQTTSuccess if the Payload Format Indicator was successfully added
 * - #MQTTBadParameter if an invalid parameter is passed
 * - #MQTTNoMemory if the property builder has insufficient space
 */
/* @[declare_mqttpropadd_payloadformat] */
MQTTStatus_t MQTTPropAdd_PayloadFormat( MQTTPropBuilder_t * pPropertyBuilder,
                                        bool payloadFormat,
                                        const uint8_t * pOptionalMqttPacketType );
/* @[declare_mqttpropadd_payloadformat] */

/**
 * @brief Adds Message Expiry Interval property to the MQTT property builder.
 *
 * This function adds Message Expiry Interval property to the property builder.
 *
 * @param[out] pPropertyBuilder   Pointer to the property builder structure.
 * @param[in]  messageExpiry     The message expiry interval in seconds.
 * @param[in]  pOptionalMqttPacketType Optional MQTT packet type for which the property
 *            is being added. The function will check whether the given property can be
 *            added to the packet type if it is provided.
 *
 * @return Returns one of the following:
 * - #MQTTSuccess if the Message Expiry Interval was successfully added
 * - #MQTTBadParameter if an invalid parameter is passed
 * - #MQTTNoMemory if the property builder has insufficient space
 */
/* @[declare_mqttpropadd_messageexpiry] */
MQTTStatus_t MQTTPropAdd_MessageExpiry( MQTTPropBuilder_t * pPropertyBuilder,
                                        uint32_t messageExpiry,
                                        const uint8_t * pOptionalMqttPacketType );
/* @[declare_mqttpropadd_messageexpiry] */

/**
 * @brief Adds Will Delay Interval property to the MQTT property builder.
 *
 * This function adds Message Expiry Interval property to the property builder.
 *
 * @param[out] pPropertyBuilder   Pointer to the property builder structure.
 * @param[in]  willDelayInterval  Will Delay Interval in seconds.
 * @param[in]  pOptionalMqttPacketType Optional MQTT packet type for which the property
 *            is being added. The function will check whether the given property can be
 *            added to the packet type if it is provided.
 *
 * @return Returns one of the following:
 * - #MQTTSuccess if the Message Expiry Interval was successfully added
 * - #MQTTBadParameter if an invalid parameter is passed
 * - #MQTTNoMemory if the property builder has insufficient space
 */
/* @[declare_mqttpropadd_willdelayinterval] */
MQTTStatus_t MQTTPropAdd_WillDelayInterval( MQTTPropBuilder_t * pPropertyBuilder,
                                            uint32_t willDelayInterval,
                                            const uint8_t * pOptionalMqttPacketType );
/* @[declare_mqttpropadd_willdelayinterval] */

/**
 * @brief Adds Topic Alias property to the MQTT property builder.
 *
 * This function adds Topic Alias property to the property builder.
 *
 * @param[out] pPropertyBuilder   Pointer to the property builder structure.
 * @param[in]  topicAlias        The topic alias value.
 * @param[in]  pOptionalMqttPacketType Optional MQTT packet type for which the property
 *            is being added. The function will check whether the given property can be
 *            added to the packet type if it is provided.
 *
 * @return Returns one of the following:
 * - #MQTTSuccess if the Topic Alias was successfully added
 * - #MQTTBadParameter if an invalid parameter is passed
 * - #MQTTNoMemory if the property builder has insufficient space
 */
/* @[declare_mqttpropadd_topicalias] */
MQTTStatus_t MQTTPropAdd_TopicAlias( MQTTPropBuilder_t * pPropertyBuilder,
                                     uint16_t topicAlias,
                                     const uint8_t * pOptionalMqttPacketType );
/* @[declare_mqttpropadd_topicalias] */

/**
 * @brief Adds Response Topic property to the MQTT property builder.
 *
 * This function adds Response Topic property to the property builder.
 *
 * @param[out] pPropertyBuilder      Pointer to the property builder structure.
 * @param[in]  responseTopic        Pointer to the response topic string.
 * @param[in]  responseTopicLength  Length of the response topic string (must be less than 65536).
 * @param[in]  pOptionalMqttPacketType Optional MQTT packet type for which the property
 *            is being added. The function will check whether the given property can be
 *            added to the packet type if it is provided.
 *
 * @return Returns one of the following:
 * - #MQTTSuccess if the Response Topic was successfully added
 * - #MQTTBadParameter if an invalid parameter is passed
 * - #MQTTNoMemory if the property builder has insufficient space
 */
/* @[declare_mqttpropadd_responsetopic] */
MQTTStatus_t MQTTPropAdd_ResponseTopic( MQTTPropBuilder_t * pPropertyBuilder,
                                        const char * responseTopic,
                                        size_t responseTopicLength,
                                        const uint8_t * pOptionalMqttPacketType );
/* @[declare_mqttpropadd_responsetopic] */
/**
 * @brief Adds Correlation Data property to the MQTT property builder.
 *
 * This function adds Correlation Data property to the property builder.
 *
 * @param[out] pPropertyBuilder      Pointer to the property builder structure.
 * @param[in]  pCorrelationData     Pointer to the correlation data.
 * @param[in]  correlationLength    Length of the correlation data (must be less than 65536).
 * @param[in]  pOptionalMqttPacketType Optional MQTT packet type for which the property
 *            is being added. The function will check whether the given property can be
 *            added to the packet type if it is provided.
 *
 * @return Returns one of the following:
 * - #MQTTSuccess if the Correlation Data was successfully added
 * - #MQTTBadParameter if an invalid parameter is passed
 * - #MQTTNoMemory if the property builder has insufficient space
 */
/* @[declare_mqttpropadd_correlationdata] */
MQTTStatus_t MQTTPropAdd_CorrelationData( MQTTPropBuilder_t * pPropertyBuilder,
                                          const void * pCorrelationData,
                                          size_t correlationLength,
                                          const uint8_t * pOptionalMqttPacketType );
/* @[declare_mqttpropadd_correlationdata] */

/**
 * @brief Adds Content Type property to the MQTT property builder.
 *
 * This function adds Content Type property to the property builder.
 *
 * @param[out] pPropertyBuilder     Pointer to the property builder structure.
 * @param[in]  contentType         Pointer to the content type string.
 * @param[in]  contentTypeLength   Length of the content type string (must be less than 65536).
 * @param[in]  pOptionalMqttPacketType Optional MQTT packet type for which the property
 *            is being added. The function will check whether the given property can be
 *            added to the packet type if it is provided.
 *
 * @return Returns one of the following:
 * - #MQTTSuccess if the Content Type was successfully added
 * - #MQTTBadParameter if an invalid parameter is passed
 * - #MQTTNoMemory if the property builder has insufficient space
 */
/* @[declare_mqttpropadd_contenttype] */
MQTTStatus_t MQTTPropAdd_ContentType( MQTTPropBuilder_t * pPropertyBuilder,
                                      const char * contentType,
                                      size_t contentTypeLength,
                                      const uint8_t * pOptionalMqttPacketType );
/* @[declare_mqttpropadd_contenttype] */

/**
 * @brief Adds Reason String property to the MQTT property builder.
 *
 * This function adds Reason String property to the property builder.
 *
 * @param[out] pPropertyBuilder      Pointer to the property builder structure.
 * @param[in]  pReasonString        Pointer to the reason string.
 * @param[in]  reasonStringLength   Length of the reason string (must be less than 65536).
 * @param[in]  pOptionalMqttPacketType Optional MQTT packet type for which the property
 *            is being added. The function will check whether the given property can be
 *            added to the packet type if it is provided.
 *
 * @return Returns one of the following:
 * - #MQTTSuccess if the Reason String was successfully added
 * - #MQTTBadParameter if an invalid parameter is passed
 * - #MQTTNoMemory if the property builder has insufficient space
 */
/* @[declare_mqttpropadd_reasonstring] */
MQTTStatus_t MQTTPropAdd_ReasonString( MQTTPropBuilder_t * pPropertyBuilder,
                                       const char * pReasonString,
                                       size_t reasonStringLength,
                                       const uint8_t * pOptionalMqttPacketType );
/* @[declare_mqttpropadd_reasonstring] */

/**
 * @brief Validates the properties of a SUBSCRIBE packet.
 *
 * This function validates the properties in the property builder for a SUBSCRIBE packet.
 *
 * @param[in] isSubscriptionIdAvailable  Boolean indicating if subscription identifiers are supported.
 * @param[in] propBuilder               Pointer to the property builder structure.
 *
 * @return Returns one of the following:
 * - #MQTTSuccess if the properties are valid
 * - #MQTTBadParameter if an invalid parameter is passed
 */
/* @[declare_mqtt_validatesubscribeproperties] */
MQTTStatus_t MQTT_ValidateSubscribeProperties( bool isSubscriptionIdAvailable,
                                               const MQTTPropBuilder_t * propBuilder );
/* @[declare_mqtt_validatesubscribeproperties] */

/**
 * @brief Updates the MQTT context with connect properties from the property builder.
 *
 * This function processes the property builder and updates the connect properties
 * in the MQTT context. It handles the conversion and validation of properties from
 * the property builder to the connect properties structure.
 *
 * @param[in] pPropBuilder Pointer to the property builder containing MQTT properties.
 *                         Must not be NULL.
 * @param[out] pConnectProperties Pointer to the connection properties structure to be updated.
 *                               Must not be NULL.
 *
 * @return Returns one of the following:
 * - #MQTTSuccess if properties were successfully updated
 * - #MQTTBadParameter, MQTTBadResponse if invalid parameters are passed
 *
 * <b>Example</b>
 * @code{c}
 * // Variables used in this example.
 * MQTTStatus_t status;
 * MQTTPropBuilder_t propBuilder = { 0 };
 * MQTTConnectionProperties_t connectionProperties = { 0 };
 *
 * // Initialize property builder with desired properties
 * // ...
 *
 * // Update connect properties
 * status = updateContextWithConnectProps( &propBuilder, &connectionProperties );
 *
 * if(status == MQTTSuccess)
 * {
 *     // Properties successfully updated in the context
 * }
 * @endcode
 */

MQTTStatus_t updateContextWithConnectProps( const MQTTPropBuilder_t * pPropBuilder,
                                            MQTTConnectionProperties_t * pConnectProperties );

/**
 * @brief Get the property type at the current index in the property builder.
 *
 * This function retrieves the property identifier byte at the specified index
 * and validates that it is a recognized MQTT v5 property type. The index is
 * not advanced by this function - use the appropriate MQTTPropGet_* function
 * to retrieve the property value and advance the index.
 *
 * @warning When iterating through properties in a loop, every property returned
 * by this function MUST be consumed by either calling the corresponding
 * MQTTPropGet_* function or #MQTT_SkipNextProperty. Failing to do so will leave
 * the index unchanged, causing an infinite loop.
 *
 * @param[in] pPropertyBuilder Property builder containing the properties.
 * @param[in] currentIndex Current index in the property builder buffer.
 * @param[out] property Pointer to store the property type identifier.
 *
 * @return #MQTTSuccess if property type is retrieved and valid;
 * #MQTTBadParameter if invalid parameters are passed, index is out of bounds,
 * or the property type is not recognized.
 */
MQTTStatus_t MQTT_GetNextPropertyType( const MQTTPropBuilder_t * pPropertyBuilder,
                                       const size_t * currentIndex,
                                       uint8_t * property );

/**
 * @brief Skip the next property in the property builder without extracting its value.
 *
 * This function advances the current index past the property at the current position
 * in the property buffer. It validates the property ID and ensures the property data
 * is within bounds, but does not extract or return the property value. This is useful
 * for iterating through properties when only specific properties need to be extracted.
 *
 * @warning When iterating through properties with #MQTT_GetNextPropertyType, you MUST
 * call this function for any property you do not handle with a MQTTPropGet_* function.
 * Without this, the index will not advance past the unhandled property, resulting in
 * an infinite loop.
 *
 * @param[in] pPropertyBuilder Pointer to the property builder containing the properties.
 * @param[in,out] currentIndex Pointer to the current index in the property buffer.
 *                             On success, updated to point to the next property.
 *
 * @return #MQTTSuccess if the property is successfully skipped;
 *         #MQTTBadParameter if parameters are invalid, property ID is unknown, or
 *         the property data extends beyond the buffer bounds;
 *         #MQTTEndOfProperties if currentIndex is already at or past the end of properties.
 *
 * <b>Example</b>
 * @code{c}
 *
 * // Variables used in this example.
 * MQTTStatus_t status;
 * MQTTPropBuilder_t propertyBuilder = { 0 };
 * size_t currentIndex = 0;
 * uint8_t propertyType;
 *
 * // Initialize property builder with received properties
 * // (initialization details out of scope for this example)
 * initializePropertyBuilder( &propertyBuilder );
 *
 * // Iterate through all properties
 * while( currentIndex < propertyBuilder.currentIndex )
 * {
 *     // Get the property type at current position
 *     status = MQTT_GetNextPropertyType( &propertyBuilder, &currentIndex, &propertyType );
 *
 *     if( status != MQTTSuccess )
 *     {
 *         break;
 *     }
 *
 *     // Only extract user properties, skip all others
 *     if( propertyType == MQTT_USER_PROPERTY_ID )
 *     {
 *         MQTTUserProperty_t userProp;
 *         status = MQTTPropGet_UserProp( &propertyBuilder, &currentIndex, &userProp );
 *         // Process user property...
 *     }
 *     else
 *     {
 *         // Skip this property
 *         status = MQTT_SkipNextProperty( &propertyBuilder, &currentIndex );
 *     }
 *
 *     if( status != MQTTSuccess )
 *     {
 *         break;
 *     }
 * }
 * @endcode
 */
MQTTStatus_t MQTT_SkipNextProperty( const MQTTPropBuilder_t * pPropertyBuilder,
                                    size_t * currentIndex );

/**
 * @brief Get User Property from property builder.
 *
 * @param[in] pPropertyBuilder Property builder to get property from.
 * @param[in,out] currentIndex Current index in the property builder buffer. Updated to next property on success.
 * @param[out] pUserProperty Pointer to store the user property key-value pair.
 *
 * @return #MQTTSuccess if property is retrieved successfully;
 * #MQTTBadParameter if invalid parameters are passed.
 */
/* @[declare_mqttpropget_userprop] */
MQTTStatus_t MQTTPropGet_UserProp( const MQTTPropBuilder_t * pPropertyBuilder,
                                   size_t * currentIndex,
                                   MQTTUserProperty_t * pUserProperty );
/* @[declare_mqttpropget_userprop] */

/**
 * @brief Get Session Expiry Interval property from property builder.
 *
 * @param[in] pPropertyBuilder Property builder to get property from.
 * @param[in,out] currentIndex Current index in the property builder buffer. Updated to next property on success.
 * @param[out] pSessionExpiry Pointer to store the session expiry interval in seconds.
 *
 * @return #MQTTSuccess if property is retrieved successfully;
 * #MQTTBadParameter if invalid parameters are passed.
 */
/* @[declare_mqttpropget_sessionexpiry] */
MQTTStatus_t MQTTPropGet_SessionExpiry( const MQTTPropBuilder_t * pPropertyBuilder,
                                        size_t * currentIndex,
                                        uint32_t * pSessionExpiry );
/* @[declare_mqttpropget_sessionexpiry] */

/**
 * @brief Get Receive Maximum property from property builder.
 *
 * @param[in] pPropertyBuilder Property builder to get property from.
 * @param[in,out] currentIndex Current index in the property builder buffer. Updated to next property on success.
 * @param[out] pReceiveMax Pointer to store the receive maximum value.
 *
 * @return #MQTTSuccess if property is retrieved successfully;
 * #MQTTBadParameter if invalid parameters are passed.
 */
/* @[declare_mqttpropget_receivemax] */
MQTTStatus_t MQTTPropGet_ReceiveMax( const MQTTPropBuilder_t * pPropertyBuilder,
                                     size_t * currentIndex,
                                     uint16_t * pReceiveMax );
/* @[declare_mqttpropget_receivemax] */

/**
 * @brief Get Maximum QoS property from property builder.
 *
 * @param[in] pPropertyBuilder Property builder to get property from.
 * @param[in,out] currentIndex Current index in the property builder buffer. Updated to next property on success.
 * @param[out] pMaxQos Pointer to store the maximum QoS level (0, 1, or 2).
 *
 * @return #MQTTSuccess if property is retrieved successfully;
 * #MQTTBadParameter if invalid parameters are passed.
 */
/* @[declare_mqttpropget_maxqos] */
MQTTStatus_t MQTTPropGet_MaxQos( const MQTTPropBuilder_t * pPropertyBuilder,
                                 size_t * currentIndex,
                                 uint8_t * pMaxQos );
/* @[declare_mqttpropget_maxqos] */

/**
 * @brief Get Retain Available property from property builder.
 *
 * @param[in] pPropertyBuilder Property builder to get property from.
 * @param[in,out] currentIndex Current index in the property builder buffer. Updated to next property on success.
 * @param[out] pRetainAvailable Pointer to store the retain available flag (0 or 1).
 *
 * @return #MQTTSuccess if property is retrieved successfully;
 * #MQTTBadParameter if invalid parameters are passed.
 */
/* @[declare_mqttpropget_retainavailable] */
MQTTStatus_t MQTTPropGet_RetainAvailable( const MQTTPropBuilder_t * pPropertyBuilder,
                                          size_t * currentIndex,
                                          uint8_t * pRetainAvailable );
/* @[declare_mqttpropget_retainavailable] */

/**
 * @brief Get Maximum Packet Size property from property builder.
 *
 * @param[in] pPropertyBuilder Property builder to get property from.
 * @param[in,out] currentIndex Current index in the property builder buffer. Updated to next property on success.
 * @param[out] pMaxPacketSize Pointer to store the maximum packet size in bytes.
 *
 * @return #MQTTSuccess if property is retrieved successfully;
 * #MQTTBadParameter if invalid parameters are passed.
 */
/* @[declare_mqttpropget_maxpacketsize] */
MQTTStatus_t MQTTPropGet_MaxPacketSize( const MQTTPropBuilder_t * pPropertyBuilder,
                                        size_t * currentIndex,
                                        uint32_t * pMaxPacketSize );
/* @[declare_mqttpropget_maxpacketsize] */

/**
 * @brief Get Assigned Client Identifier property from property builder.
 *
 * @param[in] pPropertyBuilder Property builder to get property from.
 * @param[in,out] currentIndex Current index in the property builder buffer. Updated to next property on success.
 * @param[out] pClientId Pointer to store the assigned client identifier string.
 * @param[out] pClientIdLength Pointer to store the client identifier length.
 *
 * @return #MQTTSuccess if property is retrieved successfully;
 * #MQTTBadParameter if invalid parameters are passed.
 */
/* @[declare_mqttpropget_assignedclientid] */
MQTTStatus_t MQTTPropGet_AssignedClientId( const MQTTPropBuilder_t * pPropertyBuilder,
                                           size_t * currentIndex,
                                           const char ** pClientId,
                                           size_t * pClientIdLength );
/* @[declare_mqttpropget_assignedclientid] */

/**
 * @brief Get Topic Alias Maximum property from property builder.
 *
 * @param[in] pPropertyBuilder Property builder to get property from.
 * @param[in,out] currentIndex Current index in the property builder buffer. Updated to next property on success.
 * @param[out] pTopicAliasMax Pointer to store the topic alias maximum value.
 *
 * @return #MQTTSuccess if property is retrieved successfully;
 * #MQTTBadParameter if invalid parameters are passed.
 */
/* @[declare_mqttpropget_topicaliasmax] */
MQTTStatus_t MQTTPropGet_TopicAliasMax( const MQTTPropBuilder_t * pPropertyBuilder,
                                        size_t * currentIndex,
                                        uint16_t * pTopicAliasMax );
/* @[declare_mqttpropget_topicaliasmax] */

/**
 * @brief Get Reason String property from property builder.
 *
 * @param[in] pPropertyBuilder Property builder to get property from.
 * @param[in,out] currentIndex Current index in the property builder buffer. Updated to next property on success.
 * @param[out] pReasonString Pointer to store the reason string.
 * @param[out] pReasonStringLength Pointer to store the reason string length.
 *
 * @return #MQTTSuccess if property is retrieved successfully;
 * #MQTTBadParameter if invalid parameters are passed.
 */
/* @[declare_mqttpropget_reasonstring] */
MQTTStatus_t MQTTPropGet_ReasonString( const MQTTPropBuilder_t * pPropertyBuilder,
                                       size_t * currentIndex,
                                       const char ** pReasonString,
                                       size_t * pReasonStringLength );
/* @[declare_mqttpropget_reasonstring] */

/**
 * @brief Get Wildcard Subscription Available property from property builder.
 *
 * @param[in] pPropertyBuilder Property builder to get property from.
 * @param[in,out] currentIndex Current index in the property builder buffer. Updated to next property on success.
 * @param[out] pWildcardAvailable Pointer to store the wildcard subscription available flag (0 or 1).
 *
 * @return #MQTTSuccess if property is retrieved successfully;
 * #MQTTBadParameter if invalid parameters are passed.
 */
/* @[declare_mqttpropget_wildcardid] */
MQTTStatus_t MQTTPropGet_WildcardId( const MQTTPropBuilder_t * pPropertyBuilder,
                                     size_t * currentIndex,
                                     uint8_t * pWildcardAvailable );
/* @[declare_mqttpropget_wildcardid] */

/**
 * @brief Get Subscription Identifier Available property from property builder.
 *
 * @param[in] pPropertyBuilder Property builder to get property from.
 * @param[in,out] currentIndex Current index in the property builder buffer. Updated to next property on success.
 * @param[out] pSubsIdAvailable Pointer to store the subscription identifier available flag (0 or 1).
 *
 * @return #MQTTSuccess if property is retrieved successfully;
 * #MQTTBadParameter if invalid parameters are passed.
 */
/* @[declare_mqttpropget_subsidavailable] */
MQTTStatus_t MQTTPropGet_SubsIdAvailable( const MQTTPropBuilder_t * pPropertyBuilder,
                                          size_t * currentIndex,
                                          uint8_t * pSubsIdAvailable );
/* @[declare_mqttpropget_subsidavailable] */

/**
 * @brief Get Shared Subscription Available property from property builder.
 *
 * @param[in] pPropertyBuilder Property builder to get property from.
 * @param[in,out] currentIndex Current index in the property builder buffer. Updated to next property on success.
 * @param[out] pSharedSubAvailable Pointer to store the shared subscription available flag (0 or 1).
 *
 * @return #MQTTSuccess if property is retrieved successfully;
 * #MQTTBadParameter if invalid parameters are passed.
 */
/* @[declare_mqttpropget_sharedsubavailable] */
MQTTStatus_t MQTTPropGet_SharedSubAvailable( const MQTTPropBuilder_t * pPropertyBuilder,
                                             size_t * currentIndex,
                                             uint8_t * pSharedSubAvailable );
/* @[declare_mqttpropget_sharedsubavailable] */

/**
 * @brief Get Server Keep Alive property from property builder.
 *
 * @param[in] pPropertyBuilder Property builder to get property from.
 * @param[in,out] currentIndex Current index in the property builder buffer. Updated to next property on success.
 * @param[out] pServerKeepAlive Pointer to store the server keep alive interval in seconds.
 *
 * @return #MQTTSuccess if property is retrieved successfully;
 * #MQTTBadParameter if invalid parameters are passed.
 */
/* @[declare_mqttpropget_serverkeepalive] */
MQTTStatus_t MQTTPropGet_ServerKeepAlive( const MQTTPropBuilder_t * pPropertyBuilder,
                                          size_t * currentIndex,
                                          uint16_t * pServerKeepAlive );
/* @[declare_mqttpropget_serverkeepalive] */

/**
 * @brief Get Response Information property from property builder.
 *
 * @param[in] pPropertyBuilder Property builder to get property from.
 * @param[in,out] currentIndex Current index in the property builder buffer. Updated to next property on success.
 * @param[out] pResponseInfo Pointer to store the response information string.
 * @param[out] pResponseInfoLength Pointer to store the response information length.
 *
 * @return #MQTTSuccess if property is retrieved successfully;
 * #MQTTBadParameter if invalid parameters are passed.
 */
/* @[declare_mqttpropget_responseinfo] */
MQTTStatus_t MQTTPropGet_ResponseInfo( const MQTTPropBuilder_t * pPropertyBuilder,
                                       size_t * currentIndex,
                                       const char ** pResponseInfo,
                                       size_t * pResponseInfoLength );
/* @[declare_mqttpropget_responseinfo] */

/**
 * @brief Get Server Reference property from property builder.
 *
 * @param[in] pPropertyBuilder Property builder to get property from.
 * @param[in,out] currentIndex Current index in the property builder buffer. Updated to next property on success.
 * @param[out] pServerRef Pointer to store the server reference string.
 * @param[out] pServerRefLength Pointer to store the server reference length.
 *
 * @return #MQTTSuccess if property is retrieved successfully;
 * #MQTTBadParameter if invalid parameters are passed.
 */
/* @[declare_mqttpropget_serverref] */
MQTTStatus_t MQTTPropGet_ServerRef( const MQTTPropBuilder_t * pPropertyBuilder,
                                    size_t * currentIndex,
                                    const char ** pServerRef,
                                    size_t * pServerRefLength );
/* @[declare_mqttpropget_serverref] */

/**
 * @brief Get Authentication Method property from property builder.
 *
 * @param[in] pPropertyBuilder Property builder to get property from.
 * @param[in,out] currentIndex Current index in the property builder buffer. Updated to next property on success.
 * @param[out] pAuthMethod Pointer to store the authentication method string.
 * @param[out] pAuthMethodLen Pointer to store the authentication method length.
 *
 * @return #MQTTSuccess if property is retrieved successfully;
 * #MQTTBadParameter if invalid parameters are passed.
 */
/* @[declare_mqttpropget_authmethod] */
MQTTStatus_t MQTTPropGet_AuthMethod( const MQTTPropBuilder_t * pPropertyBuilder,
                                     size_t * currentIndex,
                                     const char ** pAuthMethod,
                                     size_t * pAuthMethodLen );
/* @[declare_mqttpropget_authmethod] */

/**
 * @brief Get Authentication Data property from property builder.
 *
 * @param[in] pPropertyBuilder Property builder to get property from.
 * @param[in,out] currentIndex Current index in the property builder buffer. Updated to next property on success.
 * @param[out] pAuthData Pointer to store the authentication data.
 * @param[out] pAuthDataLen Pointer to store the authentication data length.
 *
 * @return #MQTTSuccess if property is retrieved successfully;
 * #MQTTBadParameter if invalid parameters are passed.
 */
/* @[declare_mqttpropget_authdata] */
MQTTStatus_t MQTTPropGet_AuthData( const MQTTPropBuilder_t * pPropertyBuilder,
                                   size_t * currentIndex,
                                   const char ** pAuthData,
                                   size_t * pAuthDataLen );
/* @[declare_mqttpropget_authdata] */

/**
 * @brief Get Payload Format Indicator property from property builder.
 *
 * @param[in] pPropertyBuilder Property builder to get property from.
 * @param[in,out] currentIndex Current index in the property builder buffer. Updated to next property on success.
 * @param[out] pPayloadFormat Pointer to store the payload format indicator (0=unspecified, 1=UTF-8).
 *
 * @return #MQTTSuccess if property is retrieved successfully;
 * #MQTTBadParameter if invalid parameters are passed.
 */
/* @[declare_mqttpropget_payloadformatindicator] */
MQTTStatus_t MQTTPropGet_PayloadFormatIndicator( const MQTTPropBuilder_t * pPropertyBuilder,
                                                 size_t * currentIndex,
                                                 uint8_t * pPayloadFormat );
/* @[declare_mqttpropget_payloadformatindicator] */

/**
 * @brief Get Message Expiry Interval property from property builder.
 *
 * @param[in] pPropertyBuilder Property builder to get property from.
 * @param[in,out] currentIndex Current index in the property builder buffer. Updated to next property on success.
 * @param[out] pMessageExpiry Pointer to store the message expiry interval in seconds.
 *
 * @return #MQTTSuccess if property is retrieved successfully;
 * #MQTTBadParameter if invalid parameters are passed.
 */
/* @[declare_mqttpropget_messageexpiryinterval] */
MQTTStatus_t MQTTPropGet_MessageExpiryInterval( const MQTTPropBuilder_t * pPropertyBuilder,
                                                size_t * currentIndex,
                                                uint32_t * pMessageExpiry );
/* @[declare_mqttpropget_messageexpiryinterval] */

/**
 * @brief Get Topic Alias property from property builder.
 *
 * @param[in] pPropertyBuilder Property builder to get property from.
 * @param[in,out] currentIndex Current index in the property builder buffer. Updated to next property on success.
 * @param[out] pTopicAlias Pointer to store the topic alias value.
 *
 * @return #MQTTSuccess if property is retrieved successfully;
 * #MQTTBadParameter if invalid parameters are passed.
 */
/* @[declare_mqttpropget_topicalias] */
MQTTStatus_t MQTTPropGet_TopicAlias( const MQTTPropBuilder_t * pPropertyBuilder,
                                     size_t * currentIndex,
                                     uint16_t * pTopicAlias );
/* @[declare_mqttpropget_topicalias] */

/**
 * @brief Get Response Topic property from property builder.
 *
 * @param[in] pPropertyBuilder Property builder to get property from.
 * @param[in,out] currentIndex Current index in the property builder buffer. Updated to next property on success.
 * @param[out] pResponseTopic Pointer to store the response topic string.
 * @param[out] pResponseTopicLength Pointer to store the response topic length.
 *
 * @return #MQTTSuccess if property is retrieved successfully;
 * #MQTTBadParameter if invalid parameters are passed.
 */
/* @[declare_mqttpropget_responsetopic] */
MQTTStatus_t MQTTPropGet_ResponseTopic( const MQTTPropBuilder_t * pPropertyBuilder,
                                        size_t * currentIndex,
                                        const char ** pResponseTopic,
                                        size_t * pResponseTopicLength );
/* @[declare_mqttpropget_responsetopic] */

/**
 * @brief Get Correlation Data property from property builder.
 *
 * @param[in] pPropertyBuilder Property builder to get property from.
 * @param[in,out] currentIndex Current index in the property builder buffer. Updated to next property on success.
 * @param[out] pCorrelationData Pointer to store the correlation data.
 * @param[out] pCorrelationDataLength Pointer to store the correlation data length.
 *
 * @return #MQTTSuccess if property is retrieved successfully;
 * #MQTTBadParameter if invalid parameters are passed.
 */
/* @[declare_mqttpropget_correlationdata] */
MQTTStatus_t MQTTPropGet_CorrelationData( const MQTTPropBuilder_t * pPropertyBuilder,
                                          size_t * currentIndex,
                                          const char ** pCorrelationData,
                                          size_t * pCorrelationDataLength );
/* @[declare_mqttpropget_correlationdata] */

/**
 * @brief Get Subscription Identifier property from property builder.
 *
 * @param[in] pPropertyBuilder Property builder to get property from.
 * @param[in,out] currentIndex Current index in the property builder buffer. Updated to next property on success.
 * @param[out] pSubscriptionId Pointer to store the subscription identifier (variable byte integer).
 *
 * @return #MQTTSuccess if property is retrieved successfully;
 * #MQTTBadParameter if invalid parameters are passed.
 */
/* @[declare_mqttpropget_subscriptionid] */
MQTTStatus_t MQTTPropGet_SubscriptionId( const MQTTPropBuilder_t * pPropertyBuilder,
                                         size_t * currentIndex,
                                         uint32_t * pSubscriptionId );
/* @[declare_mqttpropget_subscriptionid] */

/**
 * @brief Get the Content Type property from the property builder.
 *
 * This function extracts the Content Type property value from the property builder
 * at the specified index. The Content Type property describes the content of the
 * Application Message.
 *
 * @param[in] pPropertyBuilder Pointer to the property builder containing the properties.
 * @param[in,out] currentIndex Pointer to the current index in the property buffer.
 *                             Updated to point past the property on success.
 * @param[out] pContentType Pointer to store the extracted Content Type string.
 * @param[out] pContentTypeLength Pointer to store the length of the Content Type string.
 *
 * @return #MQTTSuccess if the property is successfully extracted;
 * #MQTTBadParameter if parameters are invalid or property is not Content Type.
 */
/* @[declare_mqttpropget_contenttype] */
MQTTStatus_t MQTTPropGet_ContentType( const MQTTPropBuilder_t * pPropertyBuilder,
                                      size_t * currentIndex,
                                      const char ** pContentType,
                                      size_t * pContentTypeLength );
/* @[declare_mqttpropget_contenttype] */

/**
 * @brief Validates the properties of a PUBLISH packet.
 *
 * This function validates the properties in the property builder for a PUBLISH packet.
 *
 * @param[in]  serverTopicAliasMax  Maximum topic alias value allowed by the server.
 * @param[in]  propBuilder          Pointer to the property builder structure.
 * @param[out] topicAlias          Pointer to store the topic alias value if present.
 *
 * @return Returns one of the following:
 * - #MQTTSuccess if the properties are valid
 * - #MQTTBadParameter if invalid parameters are passed
 * - #MQTTBadResponse if an invalid packet is read
 */
/* @[declare_mqtt_validatepublishproperties] */
MQTTStatus_t MQTT_ValidatePublishProperties( uint16_t serverTopicAliasMax,
                                             const MQTTPropBuilder_t * propBuilder,
                                             uint16_t * topicAlias );
/* @[declare_mqtt_validatepublishproperties] */

/**
 * @brief Validate the publish parameters present in the given publish structure @p pPublishInfo.
 *
 * This function must be called before #MQTT_GetPublishPacketSize in order to validate the publish parameters.
 *
 * @param[in] pPublishInfo MQTT publish packet parameters.
 * @param[in] retainAvailable Whether server allows retain or not.
 * @param[in] maxQos Maximum QoS supported by the server.
 * @param[in] topicAlias  Topic alias in the PUBLISH packet.
 * @param[in] maxPacketSize Maximum packet size allowed by the server.
 *
 * @return  #MQTTBadParameter if invalid parameters are passed;
 * #MQTTSuccess otherwise.
 *
 * <b>Example</b>
 * @code{c}
 *
 * // Variables used in this example.
 * MQTTStatus_t status;
 * MQTTPublishInfo_t publishInfo = {0};
 * uint16_t topicAlias;
 * uint8_t retainAvailable;
 * uint8_t maxQos;
 * // Set in the CONNACK packet.
 * uint32_t maxPacketSize ;
 *
 * //Set the publish info parameters.
 *
 * //Validate the publish packet
 * status = MQTT_ValidatePublishParams(&publishInfo, retainAvailable, maxQos, topicAlias, maxPacketSize);
 *
 * if( status == MQTTSuccess )
 * {
 *      // Get the packet size and serialize the publish packet.
 * }
 * @endcode
 */
/* @[declare_mqtt_validatepublishparams] */
MQTTStatus_t MQTT_ValidatePublishParams( const MQTTPublishInfo_t * pPublishInfo,
                                         uint8_t retainAvailable,
                                         uint8_t maxQos,
                                         uint16_t topicAlias,
                                         uint32_t maxPacketSize );
/* @[declare_mqtt_validatepublishparams] */

/**
 * @brief Validates the properties specified for an MQTT PUBLISH ACK packet.
 *
 * @param[in] pPropertyBuilder Pointer to the property builder structure containing unsubscribe properties.
 *
 * @return Returns one of the following:
 * - #MQTTSuccess , #MQTTBadParameter or #MQTTBadResponse.
 */
/* @[declare_mqtt_validatepublishackproperties] */
MQTTStatus_t MQTT_ValidatePublishAckProperties( const MQTTPropBuilder_t * pPropertyBuilder );
/* @[declare_mqtt_validatepublishackproperties] */

/**
 * @brief Validates the properties specified for an MQTT UNSUBSCRIBE packet.
 *
 * @param[in] pPropertyBuilder Pointer to the property builder structure containing unsubscribe properties.
 *
 * @return Returns one of the following:
 * - #MQTTSuccess , #MQTTBadParameter or #MQTTBadResponse.
 */
/* @[declare_mqtt_validateunsubscribeproperties] */
MQTTStatus_t MQTT_ValidateUnsubscribeProperties( const MQTTPropBuilder_t * pPropertyBuilder );
/* @[declare_mqtt_validateunsubscribeproperties] */

/**
 * @brief Get the size of an outgoing PUBLISH ACK packet.
 *
 * @note If no reason code is sent and property length is zero then #MQTT_SerializeAck can be used directly.
 *
 * @param[out]  pRemainingLength The remaining length of the packet to be serialized.
 * @param[out]  pPacketSize The size of the packet to be serialized.
 * @param[in]  maxPacketSize Maximum packet size allowed by the server.
 * @param[in]  ackPropertyLength The length of the properties.
 *
 * @return #MQTTBadParameter if invalid parameters are passed;
 * #MQTTSuccess otherwise.
 *
 * <b>Example</b>
 * @code{c}
 *
 * // Variables used in this example.
 * MQTTStatus_t status;
 * MQTTFixedBuffer_t fixedBuffer;
 * uint8_t buffer[ BUFFER_SIZE ];
 * MQTTAckInfo_t  ackInfo;
 * uint16_t sessionExpiry;
 *
 * fixedBuffer.pBuffer = buffer;
 * fixedBuffer.size = BUFFER_SIZE;
 * // Variables used in this example.
 * MQTTStatus_t status;
 * size_t remainingLength =0;
 * size_t packetSize = 0;
 * size_t ackPropertyLength = 0;
 * uint32_t maxPacketSize;
 * //set the parameters.
 * // Get the size requirement for the ack packet.
 * status = MQTT_GetAckPacketSize(&remainingLength,&packetSize,maxPacketSize, ackPropertyLength);
 * }
 * @endcode
 */
/* @[declare_mqtt_getackpacketsize] */
MQTTStatus_t MQTT_GetAckPacketSize( uint32_t * pRemainingLength,
                                    uint32_t * pPacketSize,
                                    uint32_t maxPacketSize,
                                    size_t ackPropertyLength );
/* @[declare_mqtt_getackpacketsize] */

/**
 * @brief Validates the properties specified for an MQTT DISCONNECT packet.
 *
 * @param[in] connectSessionExpiry The session expiry interval that was specified
 *                                in the CONNECT packet. Used to validate that the
 *                                DISCONNECT session expiry is not non-zero while
 *                                connectSessionExpiry is zero.
 * @param[in] pPropertyBuilder Pointer to the property builder structure containing subscribe properties.
 *
 * @return Returns one of the following:
 * - #MQTTSuccess , #MQTTBadParameter or #MQTTBadResponse.
 */
/* @[declare_mqtt_validatedisconnectproperties] */
MQTTStatus_t MQTT_ValidateDisconnectProperties( uint32_t connectSessionExpiry,
                                                const MQTTPropBuilder_t * pPropertyBuilder );
/* @[declare_mqtt_validatedisconnectproperties] */

/**
 * @brief Deserialize an MQTT Disconnect packet.
 *
 * @param[in] pPacket #MQTTPacketInfo_t containing the buffer.
 * @param[in] maxPacketSize Maximum packet size allowed by the client.
 * @param[out] pDisconnectInfo Struct containing disconnect reason code
 * @param[out] pPropBuffer MQTTPropBuilder_t to store the deserialized properties.
 *
 * @return #MQTTBadParameter, #MQTTBadResponse or #MQTTSuccess.
 *
 * <b>Example</b>
 * @code{c}
 *
 * // Variables used in this example.
 * MQTTStatus_t status;
 * MQTTPacketInfo_t incomingPacket;
 * MQTTReasonCodeInfo_t disconnectInfo;
 * uint32_t maxPacketSize;
 * MQTTPropBuilder_t propBuffer; // Assume this is initialized properly
 * // Receive an incoming packet and populate all fields. The details are out of scope
 * // for this example.
 * receiveIncomingPacket( &incomingPacket );
 *
 * // Deserialize disconnect information.
 * if( ( incomingPacket.type) == MQTT_PACKET_TYPE_DISCONNECT )
 * {
 *      status = MQTT_DeserializeDisconnect(&incomingPacket,
 *                                           maxPacketSize,
 *                                           &disconnectInfo,
 *                                           &propBuffer);
 *      if( status == MQTTSuccess )
 *      {
 *          // Disconnect information is available.
 *      }
 * }
 * @endcode
 */
/* @[declare_mqtt_deserializedisconnect] */
MQTTStatus_t MQTT_DeserializeDisconnect( const MQTTPacketInfo_t * pPacket,
                                         uint32_t maxPacketSize,
                                         MQTTReasonCodeInfo_t * pDisconnectInfo,
                                         MQTTPropBuilder_t * pPropBuffer );
/* @[declare_mqtt_deserializedisconnect] */

/* *INDENT-OFF* */
#ifdef __cplusplus
    }
#endif
/* *INDENT-ON* */

#endif /* ifndef CORE_MQTT_SERIALIZER_H */

// === source/include/core_mqtt.h (verbatim from upstream) ===
/*
 * coreMQTT
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

/**
 * @file core_mqtt.h
 * @brief User-facing functions of the MQTT 5.0 library.
 */
#ifndef CORE_MQTT_H
#define CORE_MQTT_H

/* *INDENT-OFF* */
#ifdef __cplusplus
    extern "C" {
#endif
/* *INDENT-ON* */

/* Include MQTT serializer library. */

/* Include transport interface. */

/**
 * @cond DOXYGEN_IGNORE
 * The current version of this library.
 *
 * If MQTT_LIBRARY_VERSION ends with + it represents the version in development
 * after the numbered release.
 */
#define MQTT_LIBRARY_VERSION    "v5.0.2"
/** @endcond */

/**
 * @ingroup mqtt_constants
 * @brief Invalid packet identifier.
 *
 * Zero is an invalid packet identifier as per MQTT 5.0 spec.
 */
#define MQTT_PACKET_ID_INVALID    ( ( uint16_t ) 0U )

/* Structures defined in this file. */
struct MQTTPubAckInfo;
struct MQTTContext;
struct MQTTDeserializedInfo;

/**
 * @ingroup mqtt_struct_types
 * @brief An opaque structure provided by the library to the #MQTTStorePacketForRetransmit function when using #MQTTStorePacketForRetransmit.
 */
typedef struct MQTTVec MQTTVec_t;

/**
 * @ingroup mqtt_callback_types
 * @brief Application provided function to query the time elapsed since a given
 * epoch in milliseconds.
 *
 * @note The timer should be a monotonic timer. It just needs to provide an
 * incrementing count of milliseconds elapsed since a given epoch.
 *
 * @note As the timer is supposed to be a millisecond timer returning a 32-bit
 * value, it will overflow in just under 50 days. But it will not cause any issues
 * in the library as the time function is only used for calculating durations for
 * timeouts and keep alive periods. The difference in unsigned numbers is
 * used where unsigned wrap around is defined. Unless the timeout is bigger than
 * 100 days (50*2) where the numbers can wrap around more than once the code
 * should work properly.
 *
 * @return The time elapsed in milliseconds.
 */
typedef uint32_t ( * MQTTGetCurrentTimeFunc_t )( void );

/**
 * @ingroup mqtt_callback_types
 * @brief Application callback for receiving incoming publishes and incoming
 * acks, as well as adding properties to outgoing publish acks.
 *
 * @note This callback will be called only if packets are deserialized with a
 * result of #MQTTSuccess or #MQTTServerRefused. The latter can be obtained
 * when deserializing a CONNACK indicating a broker's rejection of a connection.
 * For SUBACK and UNSUBACK, the deserialization result will be #MQTTSuccess even
 * when individual topic filters are rejected; the application should inspect
 * per-topic reason codes via #MQTTDeserializedInfo_t.pReasonCode.
 *
 * @param[in] pContext Initialized MQTT context.
 * @param[in] pPacketInfo Information on the type of incoming MQTT packet.
 * @param[in] pDeserializedInfo Deserialized information from incoming packet.
 * @param[out] pReasonCode Reason code for the outgoing acknowledgment. Will be NULL
 *             for terminating packets (PUBACK, PUBCOMP, SUBACK, UNSUBACK) where the
 *             library does not send a response with a reason code.
 * @param[out] pSendPropsBuffer Properties to be sent in the outgoing acknowledgment.
 *             Will be NULL for terminating packets (PUBACK, PUBCOMP, SUBACK, UNSUBACK)
 *             where the library does not send a response with properties.
 * @param[in] pGetPropsBuffer Properties received in the incoming packet.
 *
 * @note Get optional properties of incoming packets by calling these functions:
 *
 *
 * - Connack Properties:
 *  - #MQTTPropGet_SessionExpiry
 *  - #MQTTPropGet_ReceiveMax
 *  - #MQTTPropGet_MaxQos
 *  - #MQTTPropGet_RetainAvailable
 *  - #MQTTPropGet_MaxPacketSize
 *  - #MQTTPropGet_AssignedClientId
 *  - #MQTTPropGet_TopicAliasMax
 *  - #MQTTPropGet_ReasonString
 *  - #MQTTPropGet_UserProp
 *  - #MQTTPropGet_WildcardId
 *  - #MQTTPropGet_SubsIdAvailable
 *  - #MQTTPropGet_SharedSubAvailable
 *  - #MQTTPropGet_ServerKeepAlive
 *  - #MQTTPropGet_ResponseInfo
 *  - #MQTTPropGet_ServerRef
 *  - #MQTTPropGet_AuthMethod
 *  - #MQTTPropGet_AuthData
 *
 * - Publish Properties:
 *  - #MQTTPropGet_TopicAlias
 *  - #MQTTPropGet_PayloadFormatIndicator
 *  - #MQTTPropGet_ResponseTopic
 *  - #MQTTPropGet_CorrelationData
 *  - #MQTTPropGet_MessageExpiryInterval
 *  - #MQTTPropGet_ContentType
 *  - #MQTTPropGet_SubscriptionId
 *  - #MQTTPropGet_UserProp
 *
 * - Ack Properties (PUBACK, PUBREC, PUBREL, PUBCOMP, SUBACK, UNSUBACK):
 *  - #MQTTPropGet_ReasonString
 *  - #MQTTPropGet_UserProp
 *
 * - Disconnect Properties:
 *  - #MQTTPropGet_SessionExpiry
 *  - #MQTTPropGet_ReasonString
 *  - #MQTTPropGet_UserProp
 *  - #MQTTPropGet_ServerRef
 *
 * @warning When iterating through properties in pGetPropsBuffer using
 * #MQTT_GetNextPropertyType, every property MUST be consumed by either calling
 * the corresponding MQTTPropGet_* function or #MQTT_SkipNextProperty. Failing
 * to advance the index past an unhandled property will cause an infinite loop.
 *
 * @note Add optional properties to outgoing publish ack packets by calling these functions:
 *
 * - #MQTTPropAdd_UserProp
 * - #MQTTPropAdd_ReasonString
 * @return
 * - true Event callback was able to process the packet
 * - false This is not an error but just a flag that tells
 *          the user that the eventcallback was unable to process
 *          a packet due to application specific reasons.
 *          The application should recall the processloop after
 *          making sure that it would be able to process the
 *          received packet again.
 */
typedef bool ( * MQTTEventCallback_t )( struct MQTTContext * pContext,
                                        struct MQTTPacketInfo * pPacketInfo,
                                        struct MQTTDeserializedInfo * pDeserializedInfo,
                                        enum MQTTSuccessFailReasonCode * pReasonCode,
                                        struct MQTTPropBuilder * pSendPropsBuffer,
                                        struct MQTTPropBuilder * pGetPropsBuffer );

/**
 * @brief User defined callback used to store packets for retransmits. Used to track any publish/PUBREC
 * retransmit on an unclean session connection.
 *
 * @param[in] pContext Initialised MQTT Context.
 * @param[in] handle Unique 32-bit handle to distinguish the packets. Note that these values may or may not
 *                be in order. The value is interpreted by the coreMQTT library and might change in pattern.
 * @param[in] pMqttVec Pointer to the opaque mqtt vector structure. Users should use MQTT_GetBytesInMQTTVec
 *                and MQTT_SerializeMQTTVec functions to get the memory required and to serialize the
 *                MQTTVec_t in the provided memory respectively.
 *
 * @return True if the copy is successful else false.
 */
/* @[define_mqtt_retransmitstorepacket] */
typedef bool ( * MQTTStorePacketForRetransmit )( struct MQTTContext * pContext,
                                                 uint32_t handle,
                                                 MQTTVec_t * pMqttVec );
/* @[define_mqtt_retransmitstorepacket] */

/**
 * @brief User defined callback used to retreive a stored packet for resend operation. Used to
 * track any publish/PUBREC retransmit on an unclean session connection.
 *
 * @param[in] pContext Initialised MQTT Context.
 * @param[in] handle Unique 32-bit handle to distinguish the packets. Note that these values may or may not
 *                be in order. The value is interpreted by the coreMQTT library and might change in pattern.
 * @param[out] pSerializedMqttVec Output parameter to store the pointer to the serialized MQTTVec_t
 *                  using MQTT_SerializeMQTTVec.
 * @param[out] pSerializedMqttVecLen Output parameter to return the number of bytes used to store the
 *                  MQTTVec_t. This value should be the same as the one received from MQTT_GetBytesInMQTTVec
 *                  when storing the packet.
 *
 * @return True if the retreive is successful else false.
 */
/* @[define_mqtt_retransmitretrievepacket] */
typedef bool ( * MQTTRetrievePacketForRetransmit )( struct MQTTContext * pContext,
                                                    uint32_t handle,
                                                    uint8_t ** pSerializedMqttVec,
                                                    size_t * pSerializedMqttVecLen );
/* @[define_mqtt_retransmitretrievepacket] */

/**
 * @brief User defined callback used to clear a particular stored packet. Used to track any packet
 * retransmit on an unclean session connection.
 *
 * @param[in] pContext Initialised MQTT Context.
 * @param[in] handle Unique 32-bit handle to distinguish the packets. Note that these values may or may not
 *                be in order. The value is interpreted by the coreMQTT library and might change in pattern.
 */
/* @[define_mqtt_retransmitclearpacket] */
typedef void ( * MQTTClearPacketForRetransmit )( struct MQTTContext * pContext,
                                                 uint32_t handle );
/* @[define_mqtt_retransmitclearpacket] */

/**
 * @ingroup mqtt_enum_types
 * @brief Values indicating if an MQTT connection exists.
 */
typedef enum MQTTConnectionStatus
{
    MQTTNotConnected,     /**< @brief MQTT Connection is inactive. */
    MQTTConnected,        /**< @brief MQTT Connection is active. */
    MQTTDisconnectPending /**< @brief MQTT Connection needs to be disconnected as a transport error has occurred. */
} MQTTConnectionStatus_t;

/**
 * @ingroup mqtt_enum_types
 * @brief The state of QoS 1 or QoS 2 MQTT publishes, used in the state engine.
 */
typedef enum MQTTPublishState
{
    MQTTStateNull = 0,  /**< @brief An empty state with no corresponding PUBLISH. */
    MQTTPublishSend,    /**< @brief The library will send an outgoing PUBLISH packet. */
    MQTTPubAckSend,     /**< @brief The library will send a PUBACK for a received PUBLISH. */
    MQTTPubRecSend,     /**< @brief The library will send a PUBREC for a received PUBLISH. */
    MQTTPubRelSend,     /**< @brief The library will send a PUBREL for a received PUBREC. */
    MQTTPubCompSend,    /**< @brief The library will send a PUBCOMP for a received PUBREL. */
    MQTTPubAckPending,  /**< @brief The library is awaiting a PUBACK for an outgoing PUBLISH. */
    MQTTPubRecPending,  /**< @brief The library is awaiting a PUBREC for an outgoing PUBLISH. */
    MQTTPubRelPending,  /**< @brief The library is awaiting a PUBREL for an incoming PUBLISH. */
    MQTTPubCompPending, /**< @brief The library is awaiting a PUBCOMP for an outgoing PUBLISH. */
    MQTTPublishDone     /**< @brief The PUBLISH has been completed. */
} MQTTPublishState_t;

/**
 * @ingroup mqtt_enum_types
 * @brief Packet types used in acknowledging QoS 1 or QoS 2 publishes.
 */
typedef enum MQTTPubAckType
{
    MQTTPuback, /**< @brief PUBACKs are sent in response to a QoS 1 PUBLISH. */
    MQTTPubrec, /**< @brief PUBRECs are sent in response to a QoS 2 PUBLISH. */
    MQTTPubrel, /**< @brief PUBRELs are sent in response to a PUBREC. */
    MQTTPubcomp /**< @brief PUBCOMPs are sent in response to a PUBREL. */
} MQTTPubAckType_t;

/**
 * @ingroup mqtt_enum_types
 * @brief The status codes in the SUBACK response to a subscription request.
 */
typedef enum MQTTSubAckStatus
{
    MQTTSubAckSuccessQos0 = 0x00, /**< @brief Success with a maximum delivery at QoS 0. */
    MQTTSubAckSuccessQos1 = 0x01, /**< @brief Success with a maximum delivery at QoS 1. */
    MQTTSubAckSuccessQos2 = 0x02, /**< @brief Success with a maximum delivery at QoS 2. */
    MQTTSubAckFailure = 0x80      /**< @brief Failure. */
} MQTTSubAckStatus_t;

/**
 * @ingroup mqtt_struct_types
 * @brief An element of the state engine records for QoS 1 or Qos 2 publishes.
 */
typedef struct MQTTPubAckInfo
{
    uint16_t packetId;               /**< @brief The packet ID of the original PUBLISH. */
    MQTTQoS_t qos;                   /**< @brief The QoS of the original PUBLISH. */
    MQTTPublishState_t publishState; /**< @brief The current state of the publish process. */
} MQTTPubAckInfo_t;

/**
 * @ingroup mqtt_struct_types
 * @brief A struct representing an MQTT connection.
 */
typedef struct MQTTContext
{
    /**
     * @brief State engine records for outgoing publishes.
     */
    MQTTPubAckInfo_t * outgoingPublishRecords;

    /**
     * @brief State engine records for incoming publishes.
     */
    MQTTPubAckInfo_t * incomingPublishRecords;

    /**
     * @brief The maximum number of outgoing publish records.
     */
    size_t outgoingPublishRecordMaxCount;

    /**
     * @brief The maximum number of incoming publish records.
     */
    size_t incomingPublishRecordMaxCount;

    /**
     * @brief The transport interface used by the MQTT connection.
     */
    TransportInterface_t transportInterface;

    /**
     * @brief The buffer used in receiving packets from the network.
     */
    MQTTFixedBuffer_t networkBuffer;

    /**
     * @brief The buffer used to store properties for outgoing ack packets.
     */
    MQTTPropBuilder_t ackPropsBuffer;

    /**
     * @brief The next available ID for outgoing MQTT packets.
     */
    uint16_t nextPacketId;

    /**
     * @brief Whether the context currently has a connection to the broker.
     */
    MQTTConnectionStatus_t connectStatus;

    /**
     * @brief Function used to get millisecond timestamps.
     */
    MQTTGetCurrentTimeFunc_t getTime;

    /**
     * @brief Callback function used to give deserialized MQTT packets to the application.
     */
    MQTTEventCallback_t appCallback;

    /**
     * @brief Timestamp of the last packet sent by the library.
     */
    uint32_t lastPacketTxTime;

    /**
     * @brief Timestamp of the last packet received by the library.
     */
    uint32_t lastPacketRxTime;

    /**
     * @brief Whether the library sent a packet during a call of #MQTT_ProcessLoop or
     * #MQTT_ReceiveLoop.
     */
    bool controlPacketSent;

    /**
     * @brief Index to keep track of the number of bytes received in network buffer.
     */
    size_t index;

    /* Keep alive members. */
    uint16_t keepAliveIntervalSec; /**< @brief Keep Alive interval. */
    uint32_t pingReqSendTimeMs;    /**< @brief Timestamp of the last sent PINGREQ. */
    bool waitingForPingResp;       /**< @brief If the library is currently awaiting a PINGRESP. */

    /**
     * @brief Persistent Connection Properties, populated in the CONNECT and the CONNACK.
     */
    MQTTConnectionProperties_t connectionProperties;

    /**
     * @brief User defined API used to store outgoing publishes.
     */
    MQTTStorePacketForRetransmit storeFunction;

    /**
     * @brief User defined API used to retreive a copied publish for resend operation.
     */
    MQTTRetrievePacketForRetransmit retrieveFunction;

    /**
     * @brief User defined API used to clear a particular copied publish packet.
     */
    MQTTClearPacketForRetransmit clearFunction;
} MQTTContext_t;

/**
 * @ingroup mqtt_struct_types
 * @brief Struct to hold deserialized packet information for an #MQTTEventCallback_t
 * callback.
 */
typedef struct MQTTDeserializedInfo
{
    uint16_t packetIdentifier;          /**< @brief Packet ID of deserialized packet. */
    MQTTPublishInfo_t * pPublishInfo;   /**< @brief Pointer to deserialized publish info. */
    MQTTStatus_t deserializationResult; /**< @brief Return code of deserialization. */
    MQTTReasonCodeInfo_t * pReasonCode; /**< @brief Pointer to deserialized ack info. */
} MQTTDeserializedInfo_t;

/**
 * @brief Initialize an MQTT context.
 *
 * This function must be called on an #MQTTContext_t before any other function.
 *
 * @note The #MQTTGetCurrentTimeFunc_t function for querying time must be defined. If
 * there is no time implementation, it is the responsibility of the application
 * to provide a dummy function to always return 0, provide 0 timeouts for
 * all calls to #MQTT_Connect, #MQTT_ProcessLoop, and #MQTT_ReceiveLoop and configure
 * the #MQTT_RECV_POLLING_TIMEOUT_MS and #MQTT_SEND_TIMEOUT_MS configurations
 * to be 0. This will result in loop functions running for a single iteration, and
 * #MQTT_Connect relying on #MQTT_MAX_CONNACK_RECEIVE_RETRY_COUNT to receive the CONNACK packet.
 *
 * @param[in] pContext The context to initialize.
 * @param[in] pTransportInterface The transport interface to use with the context.
 * @param[in] getTimeFunction The time utility function which can return the amount of time
 *    (in milliseconds) elapsed since a given epoch. This function will be used to ensure that
 *    timeouts in the API calls are met and keep-alive messages are sent on time.
 * @param[in] userCallback The user callback to use with the context to notify about incoming
 *     packet events.
 * @param[in] pNetworkBuffer Network buffer provided for the context. This buffer will be used
 *     to receive incoming messages from the broker. This buffer must remain valid and in scope
 *     for the entire lifetime of the @p pContext and must not be used by another context and/or
 *     application.
 *
 * @return #MQTTBadParameter if invalid parameters are passed;<br>
 * #MQTTSuccess otherwise.<br>
 *
 * <b>Example</b>
 * @code{c}
 *
 * // Function for obtaining a timestamp.
 * uint32_t getTimeStampMs();
 * // Callback function for receiving packets.
 * bool eventCallback(
 *      MQTTContext_t * pContext,
 *      MQTTPacketInfo_t * pPacketInfo,
 *      MQTTDeserializedInfo_t * pDeserializedInfo,
 *      MQTTSuccessFailReasonCode_t * pReasonCode,
 *      MQTTPropBuilder_t * pSendPropsBuffer,
 *      MQTTPropBuilder_t * pGetPropsBuffer
 * );
 * // Network send.
 * int32_t networkSend( NetworkContext_t * pContext, const void * pBuffer, size_t bytes );
 * // Network receive.
 * int32_t networkRecv( NetworkContext_t * pContext, void * pBuffer, size_t bytes );
 *
 * MQTTContext_t mqttContext;
 * TransportInterface_t transport;
 * MQTTFixedBuffer_t fixedBuffer;
 * // Create a globally accessible buffer which remains in scope for the entire duration
 * // of the MQTT context.
 * uint8_t buffer[ 1024 ];
 *
 * // Clear context.
 * memset( ( void * ) &mqttContext, 0x00, sizeof( MQTTContext_t ) );
 *
 * // Set transport interface members.
 * transport.pNetworkContext = &someTransportContext;
 * transport.send = networkSend;
 * transport.recv = networkRecv;
 * transport.writev = NULL;
 *
 * // Set buffer members.
 * fixedBuffer.pBuffer = buffer;
 * fixedBuffer.size = 1024;
 *
 * status = MQTT_Init( &mqttContext, &transport, getTimeStampMs, eventCallback, &fixedBuffer );
 *
 * if( status == MQTTSuccess )
 * {
 *      // Do something with mqttContext. The transport and fixedBuffer structs were
 *      // copied into the context, so the original structs do not need to stay in scope.
 *      // However, the memory pointed to by the fixedBuffer.pBuffer must remain in scope.
 * }
 * @endcode
 */
/* @[declare_mqtt_init] */
MQTTStatus_t MQTT_Init( MQTTContext_t * pContext,
                        const TransportInterface_t * pTransportInterface,
                        MQTTGetCurrentTimeFunc_t getTimeFunction,
                        MQTTEventCallback_t userCallback,
                        const MQTTFixedBuffer_t * pNetworkBuffer );
/* @[declare_mqtt_init] */

/**
 * @brief Initialize an MQTT context for QoS > 0.
 *
 * This function must be called on an #MQTTContext_t after MQTT_Init and before any other function.
 *
 * @param[in] pContext The context to initialize.
 * @param[in] pOutgoingPublishRecords Pointer to memory which will be used to store state of outgoing
 * publishes.
 * @param[in] outgoingPublishCount Maximum number of records which can be kept in the memory
 * pointed to by @p pOutgoingPublishRecords.
 * @param[in] pIncomingPublishRecords Pointer to memory which will be used to store state of incoming
 * publishes.
 * @param[in] incomingPublishCount Maximum number of records which can be kept in the memory
 * pointed to by @p pIncomingPublishRecords.
 * @param[in] pAckPropsBuf Pointer to memory which will be used to store properties of outgoing publish-ACKS.
 * @param[in] ackPropsBufLength Length of the buffer pointed to by @p pAckPropsBuf.
 * @return #MQTTBadParameter if invalid parameters are passed;<br>
 * #MQTTSuccess otherwise.<br>
 *
 * <b>Example</b>
 * @code{c}
 *
 * // Function for obtaining a timestamp.
 * uint32_t getTimeStampMs();
 * // Callback function for receiving packets.
 * bool eventCallback(
 *      MQTTContext_t * pContext,
 *      MQTTPacketInfo_t * pPacketInfo,
 *      MQTTDeserializedInfo_t * pDeserializedInfo,
 *      MQTTSuccessFailReasonCode_t * pReasonCode,
 *      MQTTPropBuilder_t * pSendPropsBuffer,
 *      MQTTPropBuilder_t * pGetPropsBuffer
 * );
 * // Network send.
 * int32_t networkSend( NetworkContext_t * pContext, const void * pBuffer, size_t bytes );
 * // Network receive.
 * int32_t networkRecv( NetworkContext_t * pContext, void * pBuffer, size_t bytes );
 *
 * MQTTContext_t mqttContext;
 * TransportInterface_t transport;
 * MQTTFixedBuffer_t fixedBuffer;
 * uint8_t buffer[ 1024 ];
 * const size_t outgoingPublishCount = 30;
 * MQTTPubAckInfo_t outgoingPublishes[ outgoingPublishCount ];
 *
 * // Clear context.
 * memset( ( void * ) &mqttContext, 0x00, sizeof( MQTTContext_t ) );
 *
 * // Set transport interface members.
 * transport.pNetworkContext = &someTransportContext;
 * transport.send = networkSend;
 * transport.recv = networkRecv;
 * transport.writev = NULL;
 *
 * // Set buffer members.
 * fixedBuffer.pBuffer = buffer;
 * fixedBuffer.size = 1024;
 *
 * status = MQTT_Init( &mqttContext, &transport, getTimeStampMs, eventCallback, &fixedBuffer );
 *
 * if( status == MQTTSuccess )
 * {
 *      // We do not expect any incoming publishes in this example, therefore the incoming
 *      // publish pointer is NULL and the count is zero.
 *      // The buffer is used to store properties of outgoing publish-ACKS.
 *      uint8_t ackPropsBuf[ 500 ];
 *      size_t ackPropsBufLength = sizeof( ackPropsBuf );
 *      status = MQTT_InitStatefulQoS( &mqttContext,
 *                                     outgoingPublishes,
 *                                     outgoingPublishCount,
 *                                     NULL,
 *                                     0,
 *                                     ackPropsBuf,
 *                                     ackPropsBufLength );
 *
 *      // Now QoS1 and/or QoS2 publishes can be sent with this context.
 * }
 * @endcode
 */
/* @[declare_mqtt_initstatefulqos] */
MQTTStatus_t MQTT_InitStatefulQoS( MQTTContext_t * pContext,
                                   MQTTPubAckInfo_t * pOutgoingPublishRecords,
                                   size_t outgoingPublishCount,
                                   MQTTPubAckInfo_t * pIncomingPublishRecords,
                                   size_t incomingPublishCount,
                                   uint8_t * pAckPropsBuf,
                                   size_t ackPropsBufLength );
/* @[declare_mqtt_initstatefulqos] */

/**
 * @brief Initialize an MQTT context for publish retransmits for QoS > 0.
 *
 * This function must be called on an #MQTTContext_t after MQTT_InitstatefulQoS and before any other function.
 *
 * @param[in] pContext The context to initialize.
 * @param[in] storeFunction User defined API used to store outgoing publishes.
 * @param[in] retrieveFunction User defined API used to retreive a copied publish for resend operation.
 * @param[in] clearFunction User defined API used to clear a particular copied publish packet.
 *
 * @return #MQTTBadParameter if invalid parameters are passed;
 * #MQTTSuccess otherwise.
 *
 * <b>Example</b>
 * @code{c}
 *
 * // Function for obtaining a timestamp.
 * uint32_t getTimeStampMs();
 * // Callback function for receiving packets.
 * bool eventCallback(
 *      MQTTContext_t * pContext,
 *      MQTTPacketInfo_t * pPacketInfo,
 *      MQTTDeserializedInfo_t * pDeserializedInfo,
 *      MQTTSuccessFailReasonCode_t * pReasonCode,
 *      MQTTPropBuilder_t * pSendPropsBuffer,
 *      MQTTPropBuilder_t * pGetPropsBuffer
 * );
 * // Network send.
 * int32_t networkSend( NetworkContext_t * pContext, const void * pBuffer, size_t bytes );
 * // Network receive.
 * int32_t networkRecv( NetworkContext_t * pContext, void * pBuffer, size_t bytes );
 * // User defined callback used to store outgoing publishes
 * bool publishStoreCallback(struct MQTTContext* pContext,
 *                           uint16_t packetId,
 *                           MQTTVec_t* pIoVec);
 * // User defined callback used to retreive a copied publish for resend operation
 * bool publishRetrieveCallback(struct MQTTContext* pContext,
 *                              uint16_t packetId,
 *                              TransportOutVector_t** pIoVec,
 *                              size_t* ioVecCount);
 * // User defined callback used to clear a particular copied publish packet
 * bool publishClearCallback(struct MQTTContext* pContext,
 *                           uint16_t packetId);
 *
 * MQTTContext_t mqttContext;
 * TransportInterface_t transport;
 * MQTTFixedBuffer_t fixedBuffer;
 * uint8_t buffer[ 1024 ];
 * const size_t outgoingPublishCount = 30;
 * MQTTPubAckInfo_t outgoingPublishes[ outgoingPublishCount ];
 *
 * // Clear context.
 * memset( ( void * ) &mqttContext, 0x00, sizeof( MQTTContext_t ) );
 *
 * // Set transport interface members.
 * transport.pNetworkContext = &someTransportContext;
 * transport.send = networkSend;
 * transport.recv = networkRecv;
 * transport.writev = NULL;
 *
 * // Set buffer members.
 * fixedBuffer.pBuffer = buffer;
 * fixedBuffer.size = 1024;
 *
 * status = MQTT_Init( &mqttContext, &transport, getTimeStampMs, eventCallback, &fixedBuffer );
 *
 * if( status == MQTTSuccess )
 * {
 *      // We do not expect any incoming publishes in this example, therefore the incoming
 *      // publish pointer is NULL and the count is zero.
 *      uint8_t ackPropsBuf[ 500 ];
 *      size_t ackPropsBufLength = sizeof( ackPropsBuf );
 *      status = MQTT_InitStatefulQoS( &mqttContext, outgoingPublishes, outgoingPublishCount,
 *                                     NULL, 0, ackPropsBuf, ackPropsBufLength );
 *
 *      // Now QoS1 and/or QoS2 publishes can be sent with this context.
 * }
 *
 * if( status == MQTTSuccess )
 * {
 *      status = MQTT_InitRetransmits( &mqttContext, publishStoreCallback,
 *                                                   publishRetrieveCallback,
 *                                                   publishClearCallback );
 *
 *      // Now unacked Publishes can be resent on an unclean session resumption.
 * }
 * @endcode
 */

/* @[declare_mqtt_initretransmits] */
MQTTStatus_t MQTT_InitRetransmits( MQTTContext_t * pContext,
                                   MQTTStorePacketForRetransmit storeFunction,
                                   MQTTRetrievePacketForRetransmit retrieveFunction,
                                   MQTTClearPacketForRetransmit clearFunction );
/* @[declare_mqtt_initretransmits] */

/**
 * @brief Checks the MQTT connection status with the broker.
 *
 * @param[in] pContext Initialized MQTT context.
 *
 * @return #MQTTBadParameter if invalid parameters are passed;
 * #MQTTStatusConnected if the MQTT connection is established with the broker.
 * #MQTTStatusNotConnected if the MQTT connection is not established with the broker.
 * #MQTTStatusDisconnectPending if Transport Interface has failed and MQTT connection needs to be closed.
 *
 * <b>Example</b>
 * @code{c}
 *
 * @endcode
 */
/* @[declare_mqtt_checkconnectstatus] */
MQTTStatus_t MQTT_CheckConnectStatus( const MQTTContext_t * pContext );
/* @[declare_mqtt_checkconnectstatus] */

/**
 * @brief Establish an MQTT session.
 *
 * This function will send MQTT CONNECT packet and receive a CONNACK packet. The
 * send and receive from the network is done through the transport interface.
 *
 * The maximum time this function waits for a CONNACK is decided in one of the
 * following ways:
 * 1. If @p timeoutMs is greater than 0:
 *    #MQTTContext_t.getTime is used to ensure that the function does not wait
 *    more than @p timeoutMs for CONNACK.
 * 2. If @p timeoutMs is 0:
 *    The network receive for CONNACK is retried up to the number of times
 *    configured by #MQTT_MAX_CONNACK_RECEIVE_RETRY_COUNT.
 *
 * @note If a dummy #MQTTGetCurrentTimeFunc_t was passed to #MQTT_Init, then a
 * timeout value of 0 MUST be passed to the API, and the #MQTT_RECV_POLLING_TIMEOUT_MS
 * and #MQTT_SEND_TIMEOUT_MS timeout configurations MUST be set to 0.
 *
 * @param[in] pContext Initialized MQTT context.
 * @param[in] pConnectInfo MQTT CONNECT packet information.
 * @param[in] pWillInfo Last Will and Testament. Pass NULL if Last Will and
 * Testament is not used.
 * @param[in] timeoutMs Maximum time in milliseconds to wait for a CONNACK packet.
 * A zero timeout makes use of the retries for receiving CONNACK as configured with
 * #MQTT_MAX_CONNACK_RECEIVE_RETRY_COUNT.
 * @param[in] pPropertyBuilder Properties to be sent in the outgoing packet.
 * @param[in] pWillPropertyBuilder Will Properties to be sent in the outgoing packet.
 * @param[out] pSessionPresent This value will be set to true if a previous session
 * was present; otherwise it will be set to false. It is only relevant if not
 * establishing a clean session.
 *
 * @return
 * #MQTTBadParameter if invalid parameters are passed;<br>
 * #MQTTSendFailed if transport send failed;<br>
 * #MQTTRecvFailed if transport receive failed for CONNACK;<br>
 * #MQTTNoDataAvailable if no data available to receive in transport until
 * the @p timeoutMs for CONNACK;<br>
 * #MQTTStatusConnected if the connection is already established<br>
 * #MQTTStatusDisconnectPending if the user is expected to call MQTT_Disconnect
 * before calling any other API<br>
 * #MQTTPublishRetrieveFailed if on an unclean session connection, the copied
 * publishes are not retrieved successfully for retransmission<br>
 * #MQTTBadResponse if the received CONNACK packet is malformed<br>
 * #MQTTServerRefused if the server refuses the connection in the CONNACK.<br>
 * #MQTTEventCallbackFailed if the user defined callback fails.<br>
 * #MQTTSuccess otherwise.<br>
 *
 * @note If no properties are provided (by setting @p pPropertyBuilder to NULL), coreMQTT
 * will add a property to the connect packet to limit the maximum packet size that the
 * broker can send to be equal to the application provided buffer to the #MQTT_Init API.
 * This prevents the case when the packet is bigger than the buffer at which point,
 * coreMQTT cannot handle the packet, neither can it drop it as MQTT protocol doesn't
 * allow it.
 *
 * @note This API may spend more time than provided in the timeoutMS parameters in
 * certain conditions as listed below:
 *
 * 1. Timeouts are incorrectly configured - If the timeoutMS is less than the
 *    transport receive timeout and if a CONNACK packet is not received within
 *    the transport receive timeout, the API will spend the transport receive
 *    timeout (which is more time than the timeoutMs). It is the case of incorrect
 *    timeout configuration as the timeoutMs parameter passed to this API must be
 *    greater than the transport receive timeout. Please refer to the transport
 *    interface documentation for more details about timeout configurations.
 *
 * 2. Partial CONNACK packet is received right before the expiry of the timeout - It
 *    is possible that first two bytes of CONNACK packet (packet type and remaining
 *    length) are received right before the expiry of the timeoutMS. In that case,
 *    the API makes one more network receive call in an attempt to receive the remaining
 *    2 bytes. In the worst case, it can happen that the remaining 2 bytes are never
 *    received and this API will end up spending timeoutMs + transport receive timeout.
 *
 * Functions to add optional properties to the CONNECT packet are:
 *
 * Connect Properties:
 * - #MQTTPropAdd_SessionExpiry
 * - #MQTTPropAdd_ReceiveMax
 * - #MQTTPropAdd_MaxPacketSize
 * - #MQTTPropAdd_TopicAliasMax
 * - #MQTTPropAdd_RequestRespInfo
 * - #MQTTPropAdd_RequestProbInfo
 * - #MQTTPropAdd_UserProp
 * - #MQTTPropAdd_AuthMethod
 * - #MQTTPropAdd_AuthData
 *
 * Will Properties:
 * - #MQTTPropAdd_WillDelayInterval
 * - #MQTTPropAdd_PayloadFormat
 * - #MQTTPropAdd_MessageExpiry
 * - #MQTTPropAdd_ResponseTopic
 * - #MQTTPropAdd_CorrelationData
 * - #MQTTPropAdd_ContentType
 * - #MQTTPropAdd_UserProp
 *
 * <b>Example</b>
 * @code{c}
 *
 * // Variables used in this example.
 * MQTTStatus_t status;
 * MQTTConnectInfo_t connectInfo = { 0 };
 * MQTTPublishInfo_t willInfo = { 0 };
 * bool sessionPresent;
 * // This is assumed to have been initialized before calling this function.
 * MQTTContext_t * pContext;
 *
 * // True for creating a new session with broker, false if we want to resume an old one.
 * connectInfo.cleanSession = true;
 * // Client ID must be unique to broker. This field is required.
 * connectInfo.pClientIdentifier = "someClientID";
 * connectInfo.clientIdentifierLength = strlen( connectInfo.pClientIdentifier );
 *
 * // The following fields are optional.
 * // Value for keep alive.
 * connectInfo.keepAliveSeconds = 60;
 * // Optional username and password.
 * connectInfo.pUserName = "someUserName";
 * connectInfo.userNameLength = strlen( connectInfo.pUserName );
 * connectInfo.pPassword = "somePassword";
 * connectInfo.passwordLength = strlen( connectInfo.pPassword );
 *  // Optional properties to be sent in the CONNECT packet.
 * MQTTPropBuilder_t connectPropsBuilder;
 * uint8_t connectPropsBuffer[ 100 ];
 * size_t connectPropsBufferLength = sizeof( connectPropsBuffer );
 * status = MQTTPropertyBuilder_Init( &connectPropsBuilder, connectPropsBuffer, connectPropsBufferLength );
 *
 *   // Set a property in the connectPropsBuilder
 * uint32_t maxPacketSize = 100 ;
 * status = MQTTPropAdd_MaxPacketSize(&connectPropsBuilder, maxPacketSize, MQTT_PROP_VALIDATE_CONNECT);
 *
 * // The last will and testament is optional, it will be published by the broker
 * // should this client disconnect without sending a DISCONNECT packet.
 * willInfo.qos = MQTTQoS0;
 * willInfo.pTopicName = "/lwt/topic/name";
 * willInfo.topicNameLength = strlen( willInfo.pTopicName );
 * willInfo.pPayload = "LWT Message";
 * willInfo.payloadLength = strlen( "LWT Message" );
 *  // Optional Will Properties to be sent in the CONNECT packet.
 * MQTTPropBuilder_t willPropsBuilder;
 * uint8_t willPropsBuffer[ 100 ];
 * size_t willPropsBufferLength = sizeof( willPropsBuffer );
 * status = MQTTPropertyBuilder_Init( &willPropsBuilder, willPropsBuffer, willPropsBufferLength );
 *
 * // Set a property in the willPropsBuilder
 * status = MQTTPropAdd_PayloadFormat( &willPropsBuilder, 1, NULL);
 *
 * // Send the connect packet. Use 100 ms as the timeout to wait for the CONNACK packet.
 * status = MQTT_Connect( pContext, &connectInfo, &willInfo, 100, &sessionPresent, &connectPropsBuilder, &willPropsBuilder );
 *
 * if( status == MQTTSuccess )
 * {
 *      // Since we requested a clean session, this must be false
 *      assert( sessionPresent == false );
 *
 *      // Do something with the connection.
 * }
 * @endcode
 */
/* @[declare_mqtt_connect] */
MQTTStatus_t MQTT_Connect( MQTTContext_t * pContext,
                           const MQTTConnectInfo_t * pConnectInfo,
                           const MQTTPublishInfo_t * pWillInfo,
                           uint32_t timeoutMs,
                           bool * pSessionPresent,
                           MQTTPropBuilder_t * pPropertyBuilder,
                           const MQTTPropBuilder_t * pWillPropertyBuilder );
/* @[declare_mqtt_connect] */

/**
 * @brief Sends MQTT SUBSCRIBE for the given list of topic filters to
 * the broker.
 *
 * @param[in] pContext Initialized MQTT context.
 * @param[in] pSubscriptionList Array of MQTT subscription info.
 * @param[in] subscriptionCount The number of elements in @ pSubscriptionList
 * array.
 * @param[in] packetId Packet ID generated by #MQTT_GetPacketId.
 * @param[in] pPropertyBuilder Properties to be sent in the outgoing packet.
 * @return
 * #MQTTBadParameter if invalid parameters are passed;<br>
 * #MQTTBadResponse if there is an error in property parsing;<br>
 * #MQTTSendFailed if transport write failed;<br>
 * #MQTTStatusNotConnected if the connection is not established yet<br>
 * #MQTTStatusDisconnectPending if the user is expected to call MQTT_Disconnect
 * before calling any other API<br>
 * #MQTTSuccess otherwise.<br>
 *
 * Functions to add optional properties to the SUBSCRIBE packet are:
 *
 * - #MQTTPropAdd_SubscriptionId
 * - #MQTTPropAdd_UserProp
 *
 * <b>Example</b>
 * @code{c}
 *
 * // Variables used in this example.
 * MQTTStatus_t status;
 * MQTTSubscribeInfo_t subscriptionList[ NUMBER_OF_SUBSCRIPTIONS ] = { 0 };
 * uint16_t packetId;
 * // This context is assumed to be initialized and connected.
 * MQTTContext_t * pContext;
 * // This is assumed to be a list of filters we want to subscribe to.
 * const char * filters[ NUMBER_OF_SUBSCRIPTIONS ];
 *
 * // Set each subscription.
 * for( int i = 0; i < NUMBER_OF_SUBSCRIPTIONS; i++ )
 * {
 *      subscriptionList[ i ].qos = MQTTQoS0;
 *      // Each subscription needs a topic filter.
 *      subscriptionList[ i ].pTopicFilter = filters[ i ];
 *      subscriptionList[ i ].topicFilterLength = strlen( filters[ i ] );
 * }
 * // Optional Properties to be sent in the SUBSCRIBE packet
 * MQTTPropBuilder_t propertyBuilder;
 * uint8_t propertyBuffer[ 100 ];
 * size_t propertyBufferLength = sizeof( propertyBuffer );
 * status = MQTTPropertyBuilder_Init( &propertyBuilder, propertyBuffer, propertyBufferLength );
 *
 * status = MQTTPropAdd_SubscriptionId(&propertyBuilder, 1, MQTT_PROP_VALIDATE_SUBSCRIBE);
 *
 * // Obtain a new packet id for the subscription.
 * packetId = MQTT_GetPacketId( pContext );
 *
 * status = MQTT_Subscribe( pContext, &subscriptionList[ 0 ], NUMBER_OF_SUBSCRIPTIONS, packetId, &propertyBuilder );
 *
 * if( status == MQTTSuccess )
 * {
 *      // We must now call MQTT_ReceiveLoop() or MQTT_ProcessLoop() to receive the SUBACK.
 *      // If the broker accepts the subscription we can now receive publishes
 *      // on the requested topics.
 * }
 * @endcode
 */
/* @[declare_mqtt_subscribe] */

MQTTStatus_t MQTT_Subscribe( MQTTContext_t * pContext,
                             const MQTTSubscribeInfo_t * pSubscriptionList,
                             size_t subscriptionCount,
                             uint16_t packetId,
                             const MQTTPropBuilder_t * pPropertyBuilder );

/* @[declare_mqtt_subscribe] */

/**
 * @brief Publishes a message to the given topic name.
 *
 * @param[in] pContext Initialized MQTT context.
 * @param[in] pPublishInfo MQTT PUBLISH packet parameters.
 * @param[in] packetId packet ID generated by #MQTT_GetPacketId.
 * @param[in] pPropertyBuilder Properties to be sent in the outgoing packet.
 *
 * @return
 * #MQTTBadParameter if invalid parameters are passed;<br>
 * #MQTTBadResponse if there is an error in property parsing;<br>
 * #MQTTSendFailed if transport write failed;<br>
 * #MQTTStatusNotConnected if the connection is not established yet<br>
 * #MQTTStatusDisconnectPending if the user is expected to call MQTT_Disconnect
 * before calling any other API<br>
 * #MQTTNoMemory if the outgoing publish record array is full<br>
 * #MQTTStateCollision if a QoS > 0 publish with the same packet ID already
 * exists in the state records and the duplicate flag is not set<br>
 * #MQTTIllegalState if the state machine update after sending fails<br>
 * #MQTTPublishStoreFailed if the user provided callback to copy and store the
 * outgoing publish packet fails<br>
 * #MQTTSuccess otherwise.<br>
 *
 * Functions to add optional properties to the PUBLISH packet are:
 *
 * - #MQTTPropAdd_PayloadFormat
 * - #MQTTPropAdd_MessageExpiry
 * - #MQTTPropAdd_TopicAlias
 * - #MQTTPropAdd_ResponseTopic
 * - #MQTTPropAdd_CorrelationData
 * - #MQTTPropAdd_ContentType
 * - #MQTTPropAdd_UserProp
 *
 * <b>Example</b>
 * @code{c}
 *
 * // Variables used in this example.
 * MQTTStatus_t status;
 * MQTTPublishInfo_t publishInfo;
 * uint16_t packetId;
 * // This context is assumed to be initialized and connected.
 * MQTTContext_t * pContext;
 *
 * // QoS of publish.
 * publishInfo.qos = MQTTQoS1;
 * publishInfo.pTopicName = "/some/topic/name";
 * publishInfo.topicNameLength = strlen( publishInfo.pTopicName );
 * publishInfo.pPayload = "Hello World!";
 * publishInfo.payloadLength = strlen( "Hello World!" );
 * // Optional properties to be sent in the PUBLISH packet.
 * MQTTPropBuilder_t propertyBuilder;
 * uint8_t propertyBuffer[ 100 ];
 * size_t propertyBufferLength = sizeof( propertyBuffer );
 * status = MQTTPropertyBuilder_Init( &propertyBuilder, propertyBuffer, propertyBufferLength );
 *
 * // Set a property in the propertyBuilder
 * status = MQTTPropAdd_PayloadFormat( &propertyBuilder, 1, MQTT_PROP_VALIDATE_PUBLISH);
 *
 * // Packet ID is needed for QoS > 0.
 * packetId = MQTT_GetPacketId( pContext );
 *
 * status = MQTT_Publish( pContext, &publishInfo, packetId, &propertyBuilder );
 *
 * if( status == MQTTSuccess )
 * {
 *      // Since the QoS is > 0, we will need to call MQTT_ReceiveLoop()
 *      // or MQTT_ProcessLoop() to process the publish acknowledgments.
 * }
 * @endcode
 */
/* @[declare_mqtt_publish] */
MQTTStatus_t MQTT_Publish( MQTTContext_t * pContext,
                           const MQTTPublishInfo_t * pPublishInfo,
                           uint16_t packetId,
                           const MQTTPropBuilder_t * pPropertyBuilder );
/* @[declare_mqtt_publish] */

/**
 * @brief Cancels an outgoing publish callback (only for QoS > QoS0) by
 * removing it from the pending ACK list.
 *
 * @note This cannot cancel the actual publish as that might have already
 * been sent to the broker. This only removes the details of the given packet
 * ID from the list of unACKed packet. That allows the caller to free any memory
 * associated with the publish payload, topic string etc. Also, after this API
 * call, the user provided callback will not be invoked when the ACK packet is
 * received.
 *
 * @param[in] pContext Initialized MQTT context.
 * @param[in] packetId packet ID corresponding to the outstanding publish.
 *
 * @return #MQTTBadParameter if invalid parameters are passed;
 * #MQTTSuccess otherwise.
 */
/* @[declare_mqtt_cancelcallback] */
MQTTStatus_t MQTT_CancelCallback( const MQTTContext_t * pContext,
                                  uint16_t packetId );
/* @[declare_mqtt_cancelcallback] */

/**
 * @brief Sends an MQTT PINGREQ to broker.
 *
 * @param[in] pContext Initialized and connected MQTT context.
 *
 * @return #MQTTNoMemory if pBuffer is too small to hold the MQTT packet;
 * #MQTTBadParameter if invalid parameters are passed;
 * #MQTTSendFailed if transport write failed;
 * #MQTTStatusNotConnected if the connection is not established yet
 * #MQTTStatusDisconnectPending if the user is expected to call MQTT_Disconnect
 * before calling any other API
 * #MQTTSuccess otherwise.
 */
/* @[declare_mqtt_ping] */
MQTTStatus_t MQTT_Ping( MQTTContext_t * pContext );
/* @[declare_mqtt_ping] */

/**
 * @brief Sends MQTT UNSUBSCRIBE for the given list of topic filters to
 * the broker.
 *
 * @param[in] pContext Initialized MQTT context.
 * @param[in] pSubscriptionList List of MQTT subscription info.
 * @param[in] subscriptionCount The number of elements in pSubscriptionList.
 * @param[in] packetId packet ID generated by #MQTT_GetPacketId.
 * @param[in] pPropertyBuilder Properties to be sent in the outgoing packet.
 *
 * @return
 * - #MQTTBadParameter if invalid parameters are passed;<br>
 * - #MQTTBadResponse if invalid properties are parsed;<br>
 * - #MQTTSendFailed if transport write failed;<br>
 * - #MQTTStatusNotConnected if the connection is not established yet<br>
 * - #MQTTStatusDisconnectPending if the user is expected to call MQTT_Disconnect
 * before calling any other API<br>
 * - #MQTTSuccess otherwise.<br>
 *
 * Functions to add optional properties to the UNSUBSCRIBE packet are:
 *
 * - #MQTTPropAdd_UserProp
 *
 * <b>Example</b>
 * @code{c}
 *
 * // Variables used in this example.
 * MQTTStatus_t status;
 * MQTTSubscribeInfo_t unsubscribeList[ NUMBER_OF_SUBSCRIPTIONS ] = { 0 };
 * uint16_t packetId;
 * // This context is assumed to be initialized and connected.
 * MQTTContext_t * pContext;
 * // This is assumed to be a list of filters we want to unsubscribe from.
 * const char * filters[ NUMBER_OF_SUBSCRIPTIONS ];
 *
 * // Set information for each unsubscribe request.
 * for( int i = 0; i < NUMBER_OF_SUBSCRIPTIONS; i++ )
 * {
 *      unsubscribeList[ i ].pTopicFilter = filters[ i ];
 *      unsubscribeList[ i ].topicFilterLength = strlen( filters[ i ] );
 *
 *      // The QoS field of MQTT_SubscribeInfo_t is unused for unsubscribing.
 * }
 *
 * // Obtain a new packet id for the unsubscribe request.
 * packetId = MQTT_GetPacketId( pContext );
 * // Optional properties to be sent in the UNSUBSCRIBE packet.
 * MQTTPropBuilder_t propertyBuilder;
 * uint8_t propertyBuffer[ 100 ];
 * size_t propertyBufferLength = sizeof( propertyBuffer );
 * status = MQTTPropertyBuilder_Init( &propertyBuilder, propertyBuffer, propertyBufferLength );
 *
 * // Set a property in the propertyBuilder
 * MQTTUserProperty_t userProperty;
 * userProperty.pKey = "key";
 * userProperty.keyLength = strlen( userProperty.pKey );
 * userProperty.pValue = "value";
 * userProperty.valueLength = strlen( userProperty.pValue );
 *
 * status = MQTTPropAdd_UserProp( &propertyBuilder, &userProperty, MQTT_PROP_VALIDATE_UNSUBSCRIBE);
 *
 * status = MQTT_Unsubscribe( pContext, &unsubscribeList[ 0 ], NUMBER_OF_SUBSCRIPTIONS, packetId, &propertyBuilder );
 *
 * if( status == MQTTSuccess )
 * {
 *      // We must now call MQTT_ReceiveLoop() or MQTT_ProcessLoop() to receive the UNSUBACK.
 *      // After this the broker should no longer send publishes for these topics.
 * }
 * @endcode
 */
/* @[declare_mqtt_unsubscribe] */
MQTTStatus_t MQTT_Unsubscribe( MQTTContext_t * pContext,
                               const MQTTSubscribeInfo_t * pSubscriptionList,
                               size_t subscriptionCount,
                               uint16_t packetId,
                               const MQTTPropBuilder_t * pPropertyBuilder );
/* @[declare_mqtt_unsubscribe] */

/**
 * @brief Sends MQTT DISCONNECT for a given reason code
 *
 * @param[in] pContext Initialized and connected MQTT context.
 * @param[in] pPropertyBuilder Properties to be sent in the outgoing packet.
 * @param[in] pReasonCode Optional reason code to be sent in the DISCONNECT packet.
 *                If NULL, then no reason code is sent.
 *
 * @return
 * #MQTTBadParameter if invalid parameters are passed;<br>
 * #MQTTBadResponse if invalid properties are parsed;<br>
 * #MQTTSendFailed if transport send failed;<br>
 * #MQTTStatusNotConnected if the connection is not established yet.<br>
 * #MQTTSuccess otherwise.<br>
 *
 * Functions to add optional properties to the DISCONNECT packet are:
 *
 * - #MQTTPropAdd_SessionExpiry
 * - #MQTTPropAdd_ReasonString
 * - #MQTTPropAdd_UserProp
 *
 * <b>Example</b>
 * @code{c}
 *
 * // Variables used in this example.
 * MQTTStatus_t status;
 * // This context is assumed to be initialized and connected.
 * MQTTContext_t * pContext;
 * // Optional properties to be sent in the DISCONNECT packet.
 * MQTTPropBuilder_t propertyBuilder;
 * uint8_t propertyBuffer[ 100 ];
 * size_t propertyBufferLength = sizeof( propertyBuffer );
 * status = MQTTPropertyBuilder_Init( &propertyBuilder, propertyBuffer, propertyBufferLength );
 *
 * // Set a property in the propertyBuilder
 * status = MQTTPropAdd_ReasonString( &propertyBuilder, "Disconnecting", 13, MQTT_PROP_VALIDATE_DISCONNECT);
 *
 * MQTTSuccessFailReasonCode_t reason = MQTT_REASON_DISCONNECT_NORMAL_DISCONNECTION;
 * status = MQTT_Disconnect( pContext, &propertyBuilder, &reason );
 *
 * if( status == MQTTSuccess )
 * {
 *      // The DISCONNECT packet was sent successfully. The connection is now closed.
 * }
 * @endcode
 */
/* @[declare_mqtt_disconnect] */
MQTTStatus_t MQTT_Disconnect( MQTTContext_t * pContext,
                              const MQTTPropBuilder_t * pPropertyBuilder,
                              const MQTTSuccessFailReasonCode_t * pReasonCode );
/* @[declare_mqtt_disconnect] */

/**
 * @brief Loop to receive packets from the transport interface. Handles keep
 * alive.
 *
 * @note If a dummy timer function, #MQTTGetCurrentTimeFunc_t, is passed to the library,
 * then the keep-alive mechanism is not supported by the #MQTT_ProcessLoop API.
 * In that case, the #MQTT_ReceiveLoop API function should be used instead.
 *
 * @param[in] pContext Initialized and connected MQTT context.
 *
 * @note Calling this function blocks the calling context for a time period that
 * depends on the passed the configuration macros, #MQTT_RECV_POLLING_TIMEOUT_MS
 * and #MQTT_SEND_TIMEOUT_MS, and the underlying transport interface implementation
 * timeouts, unless an error occurs. The blocking period also depends on the execution time of the
 * #MQTTEventCallback_t callback supplied to the library. It is recommended that the supplied
 * #MQTTEventCallback_t callback does not contain blocking operations to prevent potential
 * non-deterministic blocking period of the #MQTT_ProcessLoop API call.
 *
 * @return #MQTTSuccess on success;
 * #MQTTNeedMoreBytes if an incomplete packet has been received. The caller
 * should call this function again (probably after a delay) to receive the
 * remaining data. Both #MQTTSuccess and #MQTTNeedMoreBytes indicate normal
 * operation — all other return values indicate an error.<br>
 * #MQTTBadParameter if context is NULL;
 * #MQTTRecvFailed if a network error occurs during reception;
 * #MQTTSendFailed if a network error occurs while sending an ACK or PINGREQ;
 * #MQTTBadResponse if an invalid packet is received;
 * #MQTTKeepAliveTimeout if the server has not sent a PINGRESP before
 * #MQTT_PINGRESP_TIMEOUT_MS milliseconds;
 * #MQTTIllegalState if an incoming QoS 1/2 publish or ack causes an
 * invalid transition for the internal state machine;
 * #MQTTNoMemory if the incoming publish record array is full when
 * receiving a QoS 1/2 publish;
 * #MQTTStatusNotConnected if the connection is not established yet and a PING
 * or an ACK is being sent;
 * #MQTTStatusDisconnectPending if the user is expected to call MQTT_Disconnect
 * before calling any other API;
 * #MQTTPublishStoreFailed if the user provided store function for
 * retransmission failed while storing an outgoing acknowledgment;
 * #MQTTEventCallbackFailed if the application callback returns false.
 *
 * <b>Example</b>
 * @code{c}
 *
 * // Variables used in this example.
 * MQTTStatus_t status;
 * // This context is assumed to be initialized and connected.
 * MQTTContext_t * pContext;
 *
 * while( true )
 * {
 *      status = MQTT_ProcessLoop( pContext );
 *
 *      if( status != MQTTSuccess && status != MQTTNeedMoreBytes )
 *      {
 *          // Determine the error. It's possible we might need to disconnect
 *          // the underlying transport connection.
 *      }
 *      else
 *      {
 *          // Other application functions.
 *      }
 * }
 * @endcode
 */
/* @[declare_mqtt_processloop] */
MQTTStatus_t MQTT_ProcessLoop( MQTTContext_t * pContext );
/* @[declare_mqtt_processloop] */

/**
 * @brief Loop to receive packets from the transport interface. Does not handle
 * keep alive.
 *
 * @note If a dummy #MQTTGetCurrentTimeFunc_t was passed to #MQTT_Init, then the
 * #MQTT_RECV_POLLING_TIMEOUT_MS and #MQTT_SEND_TIMEOUT_MS timeout configurations
 * MUST be set to 0.
 *
 * @param[in] pContext Initialized and connected MQTT context.
 *
 * @note Calling this function blocks the calling context for a time period that
 * depends on the the configuration macros, #MQTT_RECV_POLLING_TIMEOUT_MS and
 * #MQTT_SEND_TIMEOUT_MS, and the underlying transport interface implementation
 * timeouts, unless an error occurs. The blocking period also depends on the execution time of the
 * #MQTTEventCallback_t callback supplied to the library. It is recommended that the supplied
 * #MQTTEventCallback_t callback does not contain blocking operations to prevent potential
 * non-deterministic blocking period of the #MQTT_ReceiveLoop API call.
 *
 * @return #MQTTSuccess on success;
 * #MQTTNeedMoreBytes if an incomplete packet has been received. The caller
 * should call this function again (probably after a delay) to receive the
 * remaining data. Both #MQTTSuccess and #MQTTNeedMoreBytes indicate normal
 * operation — all other return values indicate an error.<br>
 * #MQTTBadParameter if context is NULL;
 * #MQTTRecvFailed if a network error occurs during reception;
 * #MQTTSendFailed if a network error occurs while sending an ACK or PINGREQ;
 * #MQTTBadResponse if an invalid packet is received;
 * #MQTTIllegalState if an incoming QoS 1/2 publish or ack causes an
 * invalid transition for the internal state machine;
 * #MQTTNoMemory if the incoming publish record array is full when
 * receiving a QoS 1/2 publish;
 * #MQTTStatusNotConnected if the connection is not established yet and an
 * ACK is being sent;
 * #MQTTStatusDisconnectPending if the user is expected to call MQTT_Disconnect
 * before calling any other API;
 * #MQTTPublishStoreFailed if the user provided store function for
 * retransmission failed while storing an outgoing acknowledgment;
 * #MQTTEventCallbackFailed if the application callback returns false.
 *
 * <b>Example</b>
 * @code{c}
 *
 * // Variables used in this example.
 * MQTTStatus_t status;
 * uint32_t keepAliveMs = 60 * 1000;
 * // This context is assumed to be initialized and connected.
 * MQTTContext_t * pContext;
 *
 * while( true )
 * {
 *      status = MQTT_ReceiveLoop( pContext );
 *
 *      if( status != MQTTSuccess && status != MQTTNeedMoreBytes )
 *      {
 *          // Determine the error. It's possible we might need to disconnect
 *          // the underlying transport connection.
 *      }
 *      else
 *      {
 *          // Since this function does not send pings, the application may need
 *          // to in order to comply with keep alive.
 *          if( ( pContext->getTime() - pContext->lastPacketTxTime ) > keepAliveMs )
 *          {
 *              status = MQTT_Ping( pContext );
 *          }
 *
 *          // Other application functions.
 *      }
 * }
 * @endcode
 */
/* @[declare_mqtt_receiveloop] */
MQTTStatus_t MQTT_ReceiveLoop( MQTTContext_t * pContext );
/* @[declare_mqtt_receiveloop] */

/**
 * @brief Get a packet ID that is valid according to the MQTT 5.0 spec.
 *
 * @param[in] pContext Initialized MQTT context.
 *
 * @return A non-zero packet ID, or zero if @p pContext is NULL.
 */
/* @[declare_mqtt_getpacketid] */
uint16_t MQTT_GetPacketId( MQTTContext_t * pContext );
/* @[declare_mqtt_getpacketid] */

/**
 * @brief A utility function that determines whether the passed topic filter and
 * topic name match according to the MQTT 5.0 protocol specification.
 *
 * @param[in] pTopicName The topic name to check.
 * @param[in] topicNameLength Length of the topic name.
 * @param[in] pTopicFilter The topic filter to check.
 * @param[in] topicFilterLength Length of topic filter.
 * @param[out] pIsMatch If the match is performed without any error, that is if the
 * return value is MQTTSuccess, then and only then the value in this parameter is valid
 * and updated. In such a case, if the topic filter and the topic name match, then this
 * value is set to true; otherwise if there is no match then it is set to false.
 *
 * @note The API assumes that the passed topic name is valid to meet the
 * requirements of the MQTT 5.0 specification. Invalid topic names (for example,
 * containing wildcard characters) should not be passed to the function.
 * Also, the API checks validity of topic filter for wildcard characters ONLY if
 * the passed topic name and topic filter do not have an exact string match.
 *
 * @return Returns one of the following:
 * - #MQTTBadParameter, if any of the input parameters is invalid.
 * - #MQTTSuccess, if the matching operation was performed.
 *
 * <b>Example</b>
 * @code{c}
 *
 * // Variables used in this example.
 * const char * pTopic = "topic/match/1";
 * const char * pFilter = "topic/#";
 * MQTTStatus_t status = MQTTSuccess;
 * bool match = false;
 *
 * status = MQTT_MatchTopic( pTopic, strlen( pTopic ), pFilter, strlen( pFilter ), &match );
 * // Our parameters were valid, so this will return success.
 * assert( status == MQTTSuccess );
 *
 * // For this specific example, we already know this value is true. This
 * // check is placed here as an example for use with variable topic names.
 * if( match )
 * {
 *      // Application can decide what to do with the matching topic name.
 * }
 * @endcode
 */
MQTTStatus_t MQTT_MatchTopic( const char * pTopicName,
                              const size_t topicNameLength,
                              const char * pTopicFilter,
                              const size_t topicFilterLength,
                              bool * pIsMatch );

/**
 * @brief Parses the payload of an MQTT SUBACK packet that contains status codes
 * corresponding to topic filter subscription requests from the original
 * subscribe packet.
 *
 * Each return code in the SUBACK packet corresponds to a topic filter in the
 * SUBSCRIBE Packet being acknowledged.
 * The status codes can be one of the following:
 *  - 0x00 - Success - Maximum QoS 0
 *  - 0x01 - Success - Maximum QoS 1
 *  - 0x02 - Success - Maximum QoS 2
 *  These are the reason codes when the server refuses the request-
 *  - 0x80 - Topic Filter Refused
 *  - 0x83 - Implementation specific error.
 *  - 0x87 - Not authorized.
 *  - 0x8F - Invalid Topic Filter.
 *  - 0x91 - Packet identifier in use.
 *  - 0x97 - Quota exceeded.
 *  - 0x9E - Shared subscriptions not supported.
 *  - 0xA1 - Subscription identifiers not supported.
 *  - 0xA2 - Wildcard subscriptions not supported.
 *
 * Refer to #MQTTSubAckStatus_t for the status codes.
 *
 * @param[in] pSubackPacket The SUBACK packet whose payload is to be parsed.
 * @param[out] pPayloadStart This is populated with the starting address
 * of the payload (or return codes for topic filters) in the SUBACK packet.
 * @param[out] pPayloadSize This is populated with the size of the payload
 * in the SUBACK packet. It represents the number of topic filters whose
 * SUBACK status is present in the packet.
 *
 * @return Returns one of the following:
 * - #MQTTBadParameter if the input SUBACK packet is invalid.<br>
 * - #MQTTBadResponse if the SUBACK property length is malformed.<br>
 * - #MQTTSuccess if parsing the payload was successful.<br>
 *
 * <b>Example</b>
 * @code{c}
 *
 * // Global variable used in this example.
 * // This is assumed to be the subscription list in the original SUBSCRIBE packet.
 * MQTTSubscribeInfo_t pSubscribes[ NUMBER_OF_SUBSCRIPTIONS ];
 *
 * // MQTT_GetSubAckStatusCodes is intended to be used from the application
 * // callback that is called by the library in MQTT_ProcessLoop or MQTT_ReceiveLoop.
 * bool eventCallback(
 *      MQTTContext_t * pContext,
 *      MQTTPacketInfo_t * pPacketInfo,
 *      MQTTDeserializedInfo_t * pDeserializedInfo
 *      MQTTSuccessFailReasonCode_t * pReasonCode,
 *      MQTTPropBuilder_t * pSendPropsBuffer,
 *      MQTTPropBuilder_t * pGetPropsBuffer
 * )
 * {
 *      MQTTStatus_t status = MQTTSuccess;
 *      uint8_t * pCodes;
 *      size_t numCodes;
 *
 *      if( pPacketInfo->type == MQTT_PACKET_TYPE_SUBACK )
 *      {
 *          status = MQTT_GetSubAckStatusCodes( pPacketInfo, &pCodes, &numCodes );
 *
 *          // Since the pointers to the payload and payload size are not NULL, and
 *          // we use the packet info struct passed to the app callback (verified
 *          // to be valid by the library), this function must return success.
 *          assert( status == MQTTSuccess );
 *          // The server must send a response code for each topic filter in the
 *          // original SUBSCRIBE packet.
 *          assert( numCodes == NUMBER_OF_SUBSCRIPTIONS );
 *
 *          for( int i = 0; i < numCodes; i++ )
 *          {
 *              // The only failure code is 0x80 = MQTTSubAckFailure.
 *              if( pCodes[ i ] == MQTTSubAckFailure )
 *              {
 *                  // The subscription failed, we may want to retry the
 *                  // subscription in pSubscribes[ i ] outside of this callback.
 *              }
 *              else
 *              {
 *                  // The subscription was granted, but the maximum QoS may be
 *                  // lower than what was requested. We can verify the granted QoS.
 *                  if( pSubscribes[ i ].qos != pCodes[ i ] )
 *                  {
 *                      LogWarn( (
 *                          "Requested QoS %u, but granted QoS %u for %s",
 *                          pSubscribes[ i ].qos, pCodes[ i ], pSubscribes[ i ].pTopicFilter
 *                      ) );
 *                  }
 *              }
 *          }
 *      }
 *      // Handle other packet types.
 * }
 * @endcode
 */
/* @[declare_mqtt_getsubackstatuscodes] */
MQTTStatus_t MQTT_GetSubAckStatusCodes( const MQTTPacketInfo_t * pSubackPacket,
                                        uint8_t ** pPayloadStart,
                                        size_t * pPayloadSize );
/* @[declare_mqtt_getsubackstatuscodes] */

/**
 * @brief Parses the payload of an MQTT UNSUBACK packet that contains status codes
 * corresponding to topic filter unsubscribe requests from the original
 * unsubscribe packet.
 *
 * Each return code in the UNSUBACK packet corresponds to a topic filter in the
 * UNSUBSCRIBE Packet being acknowledged.
 * The status codes can be one of the following:
 *  - 0x00 - Success
 *  - 0x11 - No subscription existed
 *  These are the reason codes when the server refuses the request:
 *  - 0x80 - Unspecified error
 *  - 0x83 - Implementation specific error
 *  - 0x87 - Not authorized
 *  - 0x8F - Topic Filter invalid
 *  - 0x91 - Packet Identifier in use
 *
 * @param[in] pUnsubackPacket The UNSUBACK packet whose payload is to be parsed.
 * @param[out] pPayloadStart This is populated with the starting address
 * of the payload (reason codes for topic filters) in the UNSUBACK packet.
 * @param[out] pPayloadSize This is populated with the size of the payload
 * in the UNSUBACK packet. It represents the number of topic filters whose
 * UNSUBACK status is present in the packet.
 *
 * @return Returns one of the following:
 * - #MQTTBadParameter if the input UNSUBACK packet is invalid.<br>
 * - #MQTTBadResponse if the UNSUBACK property length is malformed.<br>
 * - #MQTTSuccess if parsing the payload was successful.<br>
 *
 * <b>Example</b>
 * @code{c}
 *
 * // MQTT_GetUnsubAckStatusCodes is intended to be used from the application
 * // callback that is called by the library in MQTT_ProcessLoop or MQTT_ReceiveLoop.
 * if( pPacketInfo->type == MQTT_PACKET_TYPE_UNSUBACK )
 * {
 *      uint8_t * pCodes;
 *      size_t numCodes;
 *
 *      status = MQTT_GetUnsubAckStatusCodes( pPacketInfo, &pCodes, &numCodes );
 *
 *      if( status == MQTTSuccess )
 *      {
 *          for( int i = 0; i < numCodes; i++ )
 *          {
 *              if( pCodes[ i ] != 0x00 )
 *              {
 *                  // Unsubscribe for topic filter i was not successful.
 *              }
 *          }
 *      }
 * }
 * @endcode
 */
/* @[declare_mqtt_getunsubackstatuscodes] */
MQTTStatus_t MQTT_GetUnsubAckStatusCodes( const MQTTPacketInfo_t * pUnsubackPacket,
                                          uint8_t ** pPayloadStart,
                                          size_t * pPayloadSize );
/* @[declare_mqtt_getunsubackstatuscodes] */

/**
 * @brief Error code to string conversion for MQTT statuses.
 *
 * @param[in] status The status to convert to a string.
 *
 * @return The string representation of the status.
 */
/* @[declare_mqtt_status_strerror] */
const char * MQTT_Status_strerror( MQTTStatus_t status );
/* @[declare_mqtt_status_strerror] */

/**
 * @brief Get the bytes in a #MQTTVec pointer which can store the whole array as a an
 * MQTT packet when calling MQTT_SerializeMQTTVec( void * pAllocatedMem, MQTTVec_t *pVec ) function.
 *
 * @param[in] pVec The #MQTTVec pointer given as input to the user defined
 * #MQTTStorePacketForRetransmit callback function. Must not be NULL.
 * @param[out] pOutput The number of bytes in the vector. This value is invalid if the status is not
 * #MQTTSuccess.
 *
 * @return #MQTTSuccess when the calculation is successful. The provided #MQTTVec array can then be used to
 * set aside memory to be used with MQTT_SerializeMQTTVec( void * pAllocatedMem, MQTTVec_t *pVec ) function.
 * #MQTTBadParameter on failure.
 */
/* @[declare_mqtt_getbytesinmqttvec] */
MQTTStatus_t MQTT_GetBytesInMQTTVec( const MQTTVec_t * pVec,
                                     size_t * pOutput );
/* @[declare_mqtt_getbytesinmqttvec] */

/**
 * @brief Serialize the bytes in an array of #MQTTVec in the provided \p pAllocatedMem
 *
 * @param[in] pAllocatedMem Memory in which to serialize the data in the #MQTTVec array.
 *              It must be of size provided by MQTT_GetBytesInMQTTVec( const MQTTVec_t * pVec, size_t * pOutput ).
 *              Must not be NULL.
 * @param[in] pVec The #MQTTVec pointer given as input to the user defined
 *              #MQTTStorePacketForRetransmit callback function. Must not be NULL.
 */
/* @[declare_mqtt_serializemqttvec] */
void MQTT_SerializeMQTTVec( uint8_t * pAllocatedMem,
                            const MQTTVec_t * pVec );
/* @[declare_mqtt_serializemqttvec] */

/**
 * @brief Get a human-readable string representation of an MQTT packet type.
 *
 * This function converts an MQTT packet type byte into a corresponding
 * string representation for debugging and logging purposes.
 *
 * @param[in] packetType The MQTT packet type byte to convert.
 *
 * @return A pointer to a constant string containing the packet type name.
 * Returns "UNKNOWN" if the packet type is not recognized.
 *
 * @note The returned string is statically allocated and should not be freed.
 * @note For PUBLISH packets, the function masks the lower 4 bits (flags) and
 * returns "PUBLISH" regardless of the QoS, DUP, or RETAIN flag values.
 *
 * <b>Example</b>
 * @code{c}
 * uint8_t packetType = MQTT_PACKET_TYPE_PUBLISH;
 * const char * packetName = MQTT_GetPacketTypeString( packetType );
 * printf( "Received packet: %s\n", packetName ); // Prints "Received packet: PUBLISH"
 * @endcode
 */
const char * MQTT_GetPacketTypeString( uint8_t packetType );

/* *INDENT-OFF* */
#ifdef __cplusplus
    }
#endif
/* *INDENT-ON* */

#endif /* ifndef CORE_MQTT_H */

// === source/include/core_mqtt_state.h (verbatim from upstream) ===
/*
 * coreMQTT
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

/**
 * @file core_mqtt_state.h
 * @brief Function to keep state of MQTT PUBLISH packet deliveries.
 */
#ifndef CORE_MQTT_STATE_H
#define CORE_MQTT_STATE_H

/* *INDENT-OFF* */
#ifdef __cplusplus
    extern "C" {
#endif
/* *INDENT-ON* */

/**
 * @ingroup mqtt_constants
 * @brief Initializer value for an #MQTTStateCursor_t, indicating a search
 * should start at the beginning of a state record array
 */
#define MQTT_STATE_CURSOR_INITIALIZER    ( ( size_t ) 0 )

/**
 * @ingroup mqtt_basic_types
 * @brief Cursor for iterating through state records.
 */
typedef size_t MQTTStateCursor_t;

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this section, this enum is private.
 *
 * @brief Value indicating either send or receive.
 */
typedef enum MQTTStateOperation
{
    MQTT_SEND,
    MQTT_RECEIVE
} MQTTStateOperation_t;
/** @endcond */

/**
 * @fn MQTTStatus_t MQTT_ReserveState( const MQTTContext_t * pMqttContext, uint16_t packetId, MQTTQoS_t qos );
 * @brief Reserve an entry for an outgoing QoS 1 or Qos 2 publish.
 *
 * @param[in] pMqttContext Initialized MQTT context.
 * @param[in] packetId The ID of the publish packet.
 * @param[in] qos 1 or 2.
 *
 * @return MQTTSuccess, MQTTNoMemory, or MQTTStateCollision.
 */

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this definition, this function is private.
 */
MQTTStatus_t MQTT_ReserveState( const MQTTContext_t * pMqttContext,
                                uint16_t packetId,
                                MQTTQoS_t qos );
/** @endcond */

/**
 * @fn MQTTPublishState_t MQTT_CalculateStatePublish( MQTTStateOperation_t opType, MQTTQoS_t qos )
 * @brief Calculate the new state for a publish from its qos and operation type.
 *
 * @param[in] opType Send or Receive.
 * @param[in] qos 0, 1, or 2.
 *
 * @return The calculated state.
 */

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this definition, this function is private.
 */
MQTTPublishState_t MQTT_CalculateStatePublish( MQTTStateOperation_t opType,
                                               MQTTQoS_t qos );
/** @endcond */

/**
 * @fn MQTTStatus_t MQTT_UpdateStatePublish( const MQTTContext_t * pMqttContext, uint16_t packetId, MQTTStateOperation_t opType, MQTTQoS_t qos, MQTTPublishState_t * pNewState );
 * @brief Update the state record for a PUBLISH packet.
 *
 * @param[in] pMqttContext Initialized MQTT context.
 * @param[in] packetId ID of the PUBLISH packet.
 * @param[in] opType Send or Receive.
 * @param[in] qos 0, 1, or 2.
 * @param[out] pNewState Updated state of the publish.
 *
 * @return #MQTTBadParameter, #MQTTIllegalState, #MQTTStateCollision or
 * #MQTTSuccess.
 */

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this definition, this function is private.
 */
MQTTStatus_t MQTT_UpdateStatePublish( const MQTTContext_t * pMqttContext,
                                      uint16_t packetId,
                                      MQTTStateOperation_t opType,
                                      MQTTQoS_t qos,
                                      MQTTPublishState_t * pNewState );
/** @endcond */

/**
 * @fn MQTTStatus_t MQTT_RemoveStateRecord( const MQTTContext_t * pMqttContext, uint16_t packetId );
 * @brief Remove the state record for a PUBLISH packet.
 *
 * @param[in] pMqttContext Initialized MQTT context.
 * @param[in] packetId ID of the PUBLISH packet.
 *
 * @return #MQTTBadParameter or #MQTTSuccess.
 */

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this definition, this function is private.
 */
MQTTStatus_t MQTT_RemoveStateRecord( const MQTTContext_t * pMqttContext,
                                     uint16_t packetId );
/** @endcond */

/**
 * @fn MQTTPublishState_t MQTT_CalculateStateAck( MQTTPubAckType_t packetType, MQTTStateOperation_t opType, MQTTQoS_t qos );
 * @brief Calculate the state from a PUBACK, PUBREC, PUBREL, or PUBCOMP.
 *
 * @param[in] packetType PUBACK, PUBREC, PUBREL, or PUBCOMP.
 * @param[in] opType Send or Receive.
 * @param[in] qos 1 or 2.
 *
 * @return The calculated state.
 */

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this definition, this function is private.
 */
MQTTPublishState_t MQTT_CalculateStateAck( MQTTPubAckType_t packetType,
                                           MQTTStateOperation_t opType,
                                           MQTTQoS_t qos );
/** @endcond */

/**
 * @fn MQTTStatus_t MQTT_UpdateStateAck( const MQTTContext_t * pMqttContext, uint16_t packetId, MQTTPubAckType_t packetType, MQTTStateOperation_t opType, MQTTPublishState_t * pNewState );
 * @brief Update the state record for an ACKed publish.
 *
 * @param[in] pMqttContext Initialized MQTT context.
 * @param[in] packetId ID of the ack packet.
 * @param[in] packetType PUBACK, PUBREC, PUBREL, or PUBCOMP.
 * @param[in] opType Send or Receive.
 * @param[out] pNewState Updated state of the publish.
 *
 * @return #MQTTBadParameter if an invalid parameter is passed;
 * #MQTTBadResponse if the packet from the network is not found in the records;
 * #MQTTIllegalState if the requested update would result in an illegal transition;
 * #MQTTSuccess otherwise.
 */

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this definition, this function is private.
 */
MQTTStatus_t MQTT_UpdateStateAck( const MQTTContext_t * pMqttContext,
                                  uint16_t packetId,
                                  MQTTPubAckType_t packetType,
                                  MQTTStateOperation_t opType,
                                  MQTTPublishState_t * pNewState );
/** @endcond */

/**
 * @fn uint16_t MQTT_PubrelToResend( const MQTTContext_t * pMqttContext, MQTTStateCursor_t * pCursor, MQTTPublishState_t * pState );
 * @brief Get the packet ID of next pending PUBREL ack to be resent.
 *
 * This function will need to be called to get the packet for which a PUBREL
 * need to be sent when a session is reestablished. Calling this function
 * repeatedly until packet id is 0 will give all the packets for which
 * a PUBREL need to be resent in the correct order.
 *
 * @param[in] pMqttContext Initialized MQTT context.
 * @param[in,out] pCursor Index at which to start searching.
 * @param[out] pState State indicating that PUBREL packet need to be sent.
 */

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this definition, this function is private.
 */
uint16_t MQTT_PubrelToResend( const MQTTContext_t * pMqttContext,
                              MQTTStateCursor_t * pCursor,
                              MQTTPublishState_t * pState );
/** @endcond */

/**
 * @brief Get the packet ID of next pending publish to be resent.
 *
 * This function will need to be called to get the packet for which a publish
 * need to be sent when a session is reestablished. Calling this function
 * repeatedly until packet id is 0 will give all the packets for which
 * a publish need to be resent in the correct order.
 *
 * @param[in] pMqttContext Initialized MQTT context.
 * @param[in,out] pCursor Index at which to start searching.
 *
 * <b>Example</b>
 * @code{c}
 *
 * // For this example assume this function returns an outgoing unacknowledged
 * // QoS 1 or 2 publish from its packet identifier.
 * MQTTPublishInfo_t * getPublish( uint16_t packetID );
 *
 * // Variables used in this example.
 * MQTTStatus_t status;
 * MQTTStateCursor_t cursor = MQTT_STATE_CURSOR_INITIALIZER;
 * bool sessionPresent;
 * uint16_t packetID;
 * MQTTPublishInfo_t * pResendPublish = NULL;
 * MQTTConnectInfo_t connectInfo = { 0 };
 *
 * // This is assumed to have been initialized before the call to MQTT_Connect().
 * MQTTContext_t * pContext;
 *
 * // Set clean session to false to attempt session resumption.
 * connectInfo.cleanSession = false;
 * connectInfo.pClientIdentifier = "someClientID";
 * connectInfo.clientIdentifierLength = strlen( connectInfo.pClientIdentifier );
 * connectInfo.keepAliveSeconds = 60;
 * // Optional connect parameters are not relevant to this example.
 *
 * // Create an MQTT connection. Use 100 milliseconds as a timeout.
 * status = MQTT_Connect( pContext, &connectInfo, NULL, 100, &sessionPresent, NULL, NULL );
 *
 * if( status == MQTTSuccess )
 * {
 *      if( sessionPresent )
 *      {
 *          // Loop while packet ID is nonzero.
 *          while( ( packetID = MQTT_PublishToResend( pContext, &cursor ) ) != 0 )
 *          {
 *              // Assume this function will succeed.
 *              pResendPublish = getPublish( packetID );
 *              // Set DUP flag.
 *              pResendPublish->dup = true;
 *              status = MQTT_Publish( pContext, pResendPublish, packetID, NULL );
 *
 *              if( status != MQTTSuccess )
 *              {
 *                  // Application can decide how to handle a failure.
 *              }
 *          }
 *      }
 *      else
 *      {
 *          // The broker did not resume a session, so we can clean up the
 *          // list of outgoing publishes.
 *      }
 * }
 * @endcode
 */
/* @[declare_mqtt_publishtoresend] */
uint16_t MQTT_PublishToResend( const MQTTContext_t * pMqttContext,
                               MQTTStateCursor_t * pCursor );
/* @[declare_mqtt_publishtoresend] */

/**
 * @fn const char * MQTT_State_strerror( MQTTPublishState_t state );
 * @brief State to string conversion for state engine.
 *
 * @param[in] state The state to convert to a string.
 *
 * @return The string representation of the state.
 */

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this definition, this function is private.
 */
const char * MQTT_State_strerror( MQTTPublishState_t state );
/** @endcond */

/* *INDENT-OFF* */
#ifdef __cplusplus
    }
#endif
/* *INDENT-ON* */

#endif /* ifndef CORE_MQTT_STATE_H */

// === source/include/core_mqtt_config_defaults.h (verbatim from upstream) ===
/*
 * coreMQTT
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

/**
 * @file core_mqtt_config_defaults.h
 * @brief This represents the default values for the configuration macros
 * for the MQTT library.
 *
 * @note This file SHOULD NOT be modified. If custom values are needed for
 * any configuration macro, a core_mqtt_config.h file should be provided to
 * the MQTT library to override the default values defined in this file.
 * To use the custom config file, the MQTT_DO_NOT_USE_CUSTOM_CONFIG preprocessor
 * macro SHOULD NOT be set.
 */

#ifndef CORE_MQTT_CONFIG_DEFAULTS_H_
#define CORE_MQTT_CONFIG_DEFAULTS_H_

/* *INDENT-OFF* */
#ifdef __cplusplus
    extern "C" {
#endif
/* *INDENT-ON* */

/* MQTT_DO_NOT_USE_CUSTOM_CONFIG allows building the MQTT library
 * without a custom config. If a custom config is provided, the
 * MQTT_DO_NOT_USE_CUSTOM_CONFIG macro should not be defined. */
#ifndef MQTT_DO_NOT_USE_CUSTOM_CONFIG
/* Include custom config file before other headers. */

#endif

/* The macro definition for MQTT_DO_NOT_USE_CUSTOM_CONFIG is for Doxygen
 * documentation only. */

/**
 * @brief Define this macro to build the MQTT library without the custom config
 * file core_mqtt_config.h.
 *
 * Without the custom config, the MQTT library builds with
 * default values of config macros defined in core_mqtt_config_defaults.h file.
 *
 * If a custom config is provided, then MQTT_DO_NOT_USE_CUSTOM_CONFIG should not
 * be defined.
 */
#ifdef DOXYGEN
    #define MQTT_DO_NOT_USE_CUSTOM_CONFIG
#endif

/**
 * @ingroup mqtt_constants
 * @brief Maximum number of vectors in subscribe and unsubscribe packet.
 */
#ifndef MQTT_SUB_UNSUB_MAX_VECTORS
    #define MQTT_SUB_UNSUB_MAX_VECTORS    ( 4U )
#endif

/**
 * @brief The number of retries for receiving CONNACK.
 *
 * The MQTT_MAX_CONNACK_RECEIVE_RETRY_COUNT will be used only when the
 * timeoutMs parameter of #MQTT_Connect is passed as 0 . The transport
 * receive for CONNACK will be retried MQTT_MAX_CONNACK_RECEIVE_RETRY_COUNT
 * times before timing out. A value of 0 for this config will cause the
 * transport receive for CONNACK  to be invoked only once.
 *
 * <b>Possible values:</b> Any positive 16 bit integer. <br>
 * <b>Default value:</b> `5`
 */
#ifndef MQTT_MAX_CONNACK_RECEIVE_RETRY_COUNT
/* Default value for the CONNACK receive retries. */
    #define MQTT_MAX_CONNACK_RECEIVE_RETRY_COUNT    ( 5U )
#endif

/**
 * @brief Maximum number of milliseconds to wait for a ping response to a ping
 * request as part of the keep-alive mechanism.
 *
 * If a ping response is not received before this timeout, then
 * #MQTT_ProcessLoop will return #MQTTKeepAliveTimeout.
 *
 * @note If this value is more than half of the keep alive interval, and the
 * server does not receive the previous ping request, then it is likely that the
 * server will disconnect the client before #MQTTKeepAliveTimeout can be returned.
 *
 * @note If a dummy implementation of the #MQTTGetCurrentTimeFunc_t timer function,
 * is supplied to the library, then the keep-alive mechanism is not supported by the
 * #MQTT_ProcessLoop API function. In that case, the value of #MQTT_PINGRESP_TIMEOUT_MS
 * is irrelevant to the behavior of the library.
 *
 * <b>Possible values:</b> Any positive integer up to SIZE_MAX. <br>
 * <b>Default value:</b> `5000`
 */
#ifndef MQTT_PINGRESP_TIMEOUT_MS
/* Wait 5 seconds by default for a ping response. */
    #define MQTT_PINGRESP_TIMEOUT_MS    ( 5000U )
#endif

/**
 * @brief Maximum number of milliseconds of TX inactivity to wait
 * before initiating a PINGREQ
 *
 * @note If this value is less than the keep alive interval than
 * it will be used instead.
 *
 * <b>Possible values:</b> Any positive integer up to SIZE_MAX. <br>
 * <b>Default value:</b> '30000'
 */
#ifndef PACKET_TX_TIMEOUT_MS
    #define PACKET_TX_TIMEOUT_MS    ( 30000U )
#endif

/**
 * @brief Maximum number of milliseconds of RX inactivity to wait
 * before initiating a PINGREQ
 *
 * <b>Possible values:</b> Any positive integer up to SIZE_MAX. <br>
 * <b>Default value:</b> '30000'
 *
 */
#ifndef PACKET_RX_TIMEOUT_MS
    #define PACKET_RX_TIMEOUT_MS    ( 30000U )
#endif

/**
 * @brief The maximum duration between non-empty network reads while
 * receiving an MQTT packet via the #MQTT_ProcessLoop or #MQTT_ReceiveLoop
 * API functions.
 *
 * When an incoming MQTT packet is detected, the transport receive function
 * may be called multiple times until all of the expected number of bytes of the
 * packet are received. This timeout represents the maximum polling duration that
 * is allowed without any data reception from the network for the incoming packet.
 *
 * If the timeout expires, the #MQTT_ProcessLoop and #MQTT_ReceiveLoop functions
 * return #MQTTRecvFailed.
 *
 * @note If a dummy implementation of the #MQTTGetCurrentTimeFunc_t timer function,
 * is supplied to the library, then #MQTT_RECV_POLLING_TIMEOUT_MS MUST be set to 0.
 *
 * <b>Possible values:</b> Any positive 32 bit integer. Recommended to use a
 * small timeout value. <br>
 * <b>Default value:</b> `10`
 *
 */
#ifndef MQTT_RECV_POLLING_TIMEOUT_MS
    #define MQTT_RECV_POLLING_TIMEOUT_MS    ( 10U )
#endif

/**
 * @brief The maximum duration allowed to send an MQTT packet over the transport
 * interface.
 *
 * When sending an MQTT packet, the transport send or writev functions may be
 * called multiple times until all of the required number of bytes are sent.
 * This timeout represents the maximum duration that is allowed to send the MQTT
 * packet while calling the transport send or writev functions.
 *
 * If the timeout expires, #MQTTSendFailed will be returned by the public API
 * functions.
 *
 * @note If a dummy implementation of the #MQTTGetCurrentTimeFunc_t timer function,
 * is supplied to the library, then #MQTT_SEND_TIMEOUT_MS MUST be set to 0.
 *
 * <b>Possible values:</b> Any positive 32 bit integer. <br>
 * <b>Default value:</b> `20000`
 *
 */
#ifndef MQTT_SEND_TIMEOUT_MS
    #define MQTT_SEND_TIMEOUT_MS    ( 20000U )
#endif

#ifdef MQTT_SEND_RETRY_TIMEOUT_MS
    #error MQTT_SEND_RETRY_TIMEOUT_MS is deprecated. Instead use MQTT_SEND_TIMEOUT_MS.
#endif

/**
 * @brief Macro that is called in the MQTT library for logging "Error" level
 * messages.
 *
 * To enable error level logging in the MQTT library, this macro should be mapped to the
 * application-specific logging implementation that supports error logging.
 *
 * @note This logging macro is called in the MQTT library with parameters wrapped in
 * double parentheses to be ISO C89/C90 standard compliant. For a reference
 * POSIX implementation of the logging macros, refer to core_mqtt_config.h files, and the
 * logging-stack in demos folder of the
 * [AWS IoT Embedded C SDK repository](https://github.com/aws/aws-iot-device-sdk-embedded-C).
 *
 * <b>Default value</b>: Error logging is turned off, and no code is generated for calls
 * to the macro in the MQTT library on compilation.
 */
#ifndef LogError
    #define LogError( message )
#endif

/**
 * @brief Macro that is called in the MQTT library for logging "Warning" level
 * messages.
 *
 * To enable warning level logging in the MQTT library, this macro should be mapped to the
 * application-specific logging implementation that supports warning logging.
 *
 * @note This logging macro is called in the MQTT library with parameters wrapped in
 * double parentheses to be ISO C89/C90 standard compliant. For a reference
 * POSIX implementation of the logging macros, refer to core_mqtt_config.h files, and the
 * logging-stack in demos folder of the
 * [AWS IoT Embedded C SDK repository](https://github.com/aws/aws-iot-device-sdk-embedded-C/).
 *
 * <b>Default value</b>: Warning logs are turned off, and no code is generated for calls
 * to the macro in the MQTT library on compilation.
 */
#ifndef LogWarn
    #define LogWarn( message )
#endif

/**
 * @brief Macro that is called in the MQTT library for logging "Info" level
 * messages.
 *
 * To enable info level logging in the MQTT library, this macro should be mapped to the
 * application-specific logging implementation that supports info logging.
 *
 * @note This logging macro is called in the MQTT library with parameters wrapped in
 * double parentheses to be ISO C89/C90 standard compliant. For a reference
 * POSIX implementation of the logging macros, refer to core_mqtt_config.h files, and the
 * logging-stack in demos folder of the
 * [AWS IoT Embedded C SDK repository](https://github.com/aws/aws-iot-device-sdk-embedded-C/).
 *
 * <b>Default value</b>: Info logging is turned off, and no code is generated for calls
 * to the macro in the MQTT library on compilation.
 */
#ifndef LogInfo
    #define LogInfo( message )
#endif

/**
 * @brief Macro that is called in the MQTT library for logging "Debug" level
 * messages.
 *
 * To enable debug level logging from MQTT library, this macro should be mapped to the
 * application-specific logging implementation that supports debug logging.
 *
 * @note This logging macro is called in the MQTT library with parameters wrapped in
 * double parentheses to be ISO C89/C90 standard compliant. For a reference
 * POSIX implementation of the logging macros, refer to core_mqtt_config.h files, and the
 * logging-stack in demos folder of the
 * [AWS IoT Embedded C SDK repository](https://github.com/aws/aws-iot-device-sdk-embedded-C/).
 *
 * <b>Default value</b>: Debug logging is turned off, and no code is generated for calls
 * to the macro in the MQTT library on compilation.
 */
#ifndef LogDebug
    #define LogDebug( message )
#endif

/**
 * @brief Macro that is called in the MQTT library for logging "Trace" level
 * messages.
 *
 * To enable trace level logging from MQTT library, this macro should be mapped to the
 * application-specific logging implementation that supports trace logging.
 *
 * @note This logging macro is called in the MQTT library with parameters wrapped in
 * double parentheses to be ISO C89/C90 standard compliant. For a reference
 * POSIX implementation of the logging macros, refer to core_mqtt_config.h files, and the
 * logging-stack in demos folder of the
 * [AWS IoT Embedded C SDK repository](https://github.com/aws/aws-iot-device-sdk-embedded-C/).
 *
 * <b>Default value</b>: Trace logging is turned off, and no code is generated for calls
 * to the macro in the MQTT library on compilation.
 */
#ifndef LogTrace
    #define LogTrace( message )
#endif

/* *INDENT-OFF* */
#ifdef __cplusplus
    }
#endif
/* *INDENT-ON* */

#endif /* ifndef CORE_MQTT_CONFIG_DEFAULTS_H_ */

// === source/include/private/core_mqtt_serializer_private.h (verbatim from upstream) ===
/*
 * coreMQTT
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

/**
 * @file core_mqtt_serializer_private.h
 * @brief Declares the private functions/macros to be used with serialization and
 * deserialization by the core_mqtt library.
 * DO NOT include this in your application.
 *
 * @note These functions should not be called by the application or relied upon
 *       since their implementation can change. These are for internal use by the
 *       library only.
 */
#ifndef CORE_MQTT_SERIALIZER_PRIVATE_H
#define CORE_MQTT_SERIALIZER_PRIVATE_H

#include <stdint.h>

/**
 * @brief Position of the properties for the fieldSet.
 *
 * Each property that can be added to an MQTT packet is assigned a unique bit
 * position (0–31). This macro defines the position of the property
 * in the `fieldSet` bitfield of the `MQTTPropBuilder_t` struct.
 *
 * The `fieldSet` is used to track which properties have already been added to prevent
 * duplication, as many MQTT v5 properties must not appear more than once in a packet.
 */

/**
 * @brief Defines the position of the **Subscription Identifier**
 * property in the `fieldSet` bitfield of the `MQTTPropBuilder_t` struct.
 */
#define MQTT_SUBSCRIPTION_ID_POS                    ( 1 )

/**
 * @brief Defines the position of the **Session Expiry Interval**
 * property in the `fieldSet` bitfield of the `MQTTPropBuilder_t` struct.
 */
#define MQTT_SESSION_EXPIRY_INTERVAL_POS            ( 2 )

/**
 * @brief Defines the position of the **Receive Maximum**
 * property in the `fieldSet` bitfield of the `MQTTPropBuilder_t` struct.
 */
#define MQTT_RECEIVE_MAXIMUM_POS                    ( 3 )

/**
 * @brief Defines the position of the **Maximum Packet Size**
 * property in the `fieldSet` bitfield of the `MQTTPropBuilder_t` struct.
 */
#define MQTT_MAX_PACKET_SIZE_POS                    ( 4 )

/**
 * @brief Defines the position of the **Topic Alias Maximum**
 * property in the `fieldSet` bitfield of the `MQTTPropBuilder_t` struct.
 */
#define MQTT_TOPIC_ALIAS_MAX_POS                    ( 5 )

/**
 * @brief Defines the position of the **Request Response Information**
 * property in the `fieldSet` bitfield of the `MQTTPropBuilder_t` struct.
 */
#define MQTT_REQUEST_RESPONSE_INFO_POS              ( 6 )

/**
 * @brief Defines the position of the **Request Problem Information**
 * property in the `fieldSet` bitfield of the `MQTTPropBuilder_t` struct.
 */
#define MQTT_REQUEST_PROBLEM_INFO_POS               ( 7 )

/**
 * @brief Defines the position of the **Authentication Method**
 * property in the `fieldSet` bitfield of the `MQTTPropBuilder_t` struct.
 */
#define MQTT_AUTHENTICATION_METHOD_POS              ( 9 )

/**
 * @brief Defines the position of the **Authentication Data**
 * property in the `fieldSet` bitfield of the `MQTTPropBuilder_t` struct.
 */
#define MQTT_AUTHENTICATION_DATA_POS                ( 10 )

/**
 * @brief Defines the position of the **Payload Format Indicator**
 * property in the `fieldSet` bitfield of the `MQTTPropBuilder_t` struct.
 */
#define MQTT_PAYLOAD_FORMAT_INDICATOR_POS           ( 11 )

/**
 * @brief Defines the position of the **Message Expiry Interval**
 * property in the `fieldSet` bitfield of the `MQTTPropBuilder_t` struct.
 */
#define MQTT_MESSAGE_EXPIRY_INTERVAL_POS            ( 12 )

/**
 * @brief Defines the position of the **Topic Alias**
 * property in the `fieldSet` bitfield of the `MQTTPropBuilder_t` struct.
 */
#define MQTT_TOPIC_ALIAS_POS                        ( 13 )

/**
 * @brief Defines the position of the **Response Topic**
 * property in the `fieldSet` bitfield of the `MQTTPropBuilder_t` struct.
 */
#define MQTT_RESPONSE_TOPIC_POS                     ( 14 )

/**
 * @brief Defines the position of the **Correlation Data**
 * property in the `fieldSet` bitfield of the `MQTTPropBuilder_t` struct.
 */
#define MQTT_CORRELATION_DATA_POS                   ( 15 )

/**
 * @brief Defines the position of the **Content Type**
 * property in the `fieldSet` bitfield of the `MQTTPropBuilder_t` struct.
 */
#define MQTT_CONTENT_TYPE_POS                       ( 16 )

/**
 * @brief Defines the position of the **Reason String**
 * property in the `fieldSet` bitfield of the `MQTTPropBuilder_t` struct.
 */
#define MQTT_REASON_STRING_POS                      ( 17 )

/**
 * @brief Defines the position of the **Will Delay Interval**
 * property in the `fieldSet` bitfield of the `MQTTPropBuilder_t` struct.
 */
#define MQTT_WILL_DELAY_POS                         ( 18 )

/**
 * @brief Defines the position of the **Assigned Client Identifier**
 * property in the `fieldSet` bitfield of the `MQTTPropBuilder_t` struct.
 */
#define MQTT_ASSIGNED_CLIENT_ID_POS                 ( 19 )

/**
 * @brief Defines the position of the **Server Keep Alive**
 * property in the `fieldSet` bitfield of the `MQTTPropBuilder_t` struct.
 */
#define MQTT_SERVER_KEEP_ALIVE_POS                  ( 20 )

/**
 * @brief Defines the position of the **Response Information**
 * property in the `fieldSet` bitfield of the `MQTTPropBuilder_t` struct.
 */
#define MQTT_RESPONSE_INFORMATION_POS               ( 21 )

/**
 * @brief Defines the position of the **Server Reference**
 * property in the `fieldSet` bitfield of the `MQTTPropBuilder_t` struct.
 */
#define MQTT_SERVER_REFERENCE_POS                   ( 22 )

/**
 * @brief Defines the position of the **Maximum QoS**
 * property in the `fieldSet` bitfield of the `MQTTPropBuilder_t` struct.
 */
#define MQTT_MAX_QOS_POS                            ( 23 )

/**
 * @brief Defines the position of the **Retain Available**
 * property in the `fieldSet` bitfield of the `MQTTPropBuilder_t` struct.
 */
#define MQTT_RETAIN_AVAILABLE_POS                   ( 24 )

/**
 * @brief Defines the position of the **Wildcard Subscription Available**
 * property in the `fieldSet` bitfield of the `MQTTPropBuilder_t` struct.
 */
#define MQTT_WILDCARD_SUBSCRIPTION_AVAILABLE_POS    ( 25 )

/**
 * @brief Defines the position of the **Subscription Identifier Available**
 * property in the `fieldSet` bitfield of the `MQTTPropBuilder_t` struct.
 */
#define MQTT_SUBSCRIPTION_ID_AVAILABLE_POS          ( 26 )

/**
 * @brief Defines the position of the **Shared Subscription Available**
 * property in the `fieldSet` bitfield of the `MQTTPropBuilder_t` struct.
 */
#define MQTT_SHARED_SUBSCRIPTION_AVAILABLE_POS      ( 27 )

/**
 * @brief Defines the position of the **User property**
 * in the `fieldSet` bitfield of the `MQTTPropBuilder_t` struct.
 */
#define MQTT_USER_PROP_POS                          ( 28 )

/* MQTT CONNECT flags. */
#define MQTT_CONNECT_FLAG_CLEAN                     ( 1 )     /**< @brief Clean session. */
#define MQTT_CONNECT_FLAG_WILL                      ( 2 )     /**< @brief Will present. */
#define MQTT_CONNECT_FLAG_WILL_QOS1                 ( 3 )     /**< @brief Will QoS 1. */
#define MQTT_CONNECT_FLAG_WILL_QOS2                 ( 4 )     /**< @brief Will QoS 2. */
#define MQTT_CONNECT_FLAG_WILL_RETAIN               ( 5 )     /**< @brief Will retain. */
#define MQTT_CONNECT_FLAG_PASSWORD                  ( 6 )     /**< @brief Password present. */
#define MQTT_CONNECT_FLAG_USERNAME                  ( 7 )     /**< @brief User name present. */

/**
 * @brief Macro for decoding a 4-byte unsigned int from a sequence of bytes.
 *
 * @param[in] ptr A uint8_t* that points to the high byte.
 */
#define UINT32_DECODE( ptr )                             \
    ( uint32_t ) ( ( ( ( uint32_t ) ptr[ 0 ] ) << 24 ) | \
                   ( ( ( uint32_t ) ptr[ 1 ] ) << 16 ) | \
                   ( ( ( uint32_t ) ptr[ 2 ] ) << 8 ) |  \
                   ( ( uint32_t ) ptr[ 3 ] ) )

/**
 * This macro serializes a 32-bit unsigned integer (`val`) into 4 bytes at the
 * specified memory location (`addr`).
 */
#define WRITE_UINT32( addr, val )                                  \
    {                                                              \
        ( addr )[ 3 ] = ( uint8_t ) ( ( ( val ) >> 0 ) & 0xFFU );  \
        ( addr )[ 2 ] = ( uint8_t ) ( ( ( val ) >> 8 ) & 0xFFU );  \
        ( addr )[ 1 ] = ( uint8_t ) ( ( ( val ) >> 16 ) & 0xFFU ); \
        ( addr )[ 0 ] = ( uint8_t ) ( ( ( val ) >> 24 ) & 0xFFU ); \
    }

/**
 * @brief Set a bit in an 8-bit unsigned integer.
 */
#define UINT8_SET_BIT( x, position )      ( ( x ) = ( uint8_t ) ( ( x ) | ( 0x01U << ( position ) ) ) )

/**
 * @brief Clear a bit in an 8-bit unsigned integer.
 */
#define UINT8_CLEAR_BIT( x, position )    ( ( x ) = ( uint8_t ) ( ( x ) & ( ~( 0x01U << ( position ) ) ) ) )

/**
 * @brief Macro for checking if a bit is set in a 1-byte unsigned int.
 *
 * @param[in] x The unsigned int to check.
 * @param[in] position Which bit to check.
 */
#define UINT8_CHECK_BIT( x, position )    ( ( ( x ) & ( 0x01U << ( position ) ) ) == ( 0x01U << ( position ) ) )

/**
 * @brief Get the high byte of a 16-bit unsigned integer.
 */
#define UINT16_HIGH_BYTE( x )             ( ( uint8_t ) ( ( x ) >> 8 ) )

/**
 * @brief Get the low byte of a 16-bit unsigned integer.
 */
#define UINT16_LOW_BYTE( x )              ( ( uint8_t ) ( ( x ) & 0x00ffU ) )

/**
 * @brief Macro for decoding a 2-byte unsigned int from a sequence of bytes.
 *
 * @param[in] ptr A uint8_t* that points to the high byte.
 */
#define UINT16_DECODE( ptr )                            \
    ( uint16_t ) ( ( ( ( uint16_t ) ptr[ 0 ] ) << 8 ) | \
                   ( ( uint16_t ) ptr[ 1 ] ) )

/**
 * @brief Set a bit in an 32-bit unsigned integer.
 */
#define UINT32_SET_BIT( x, position ) \
    ( ( x ) = ( uint32_t ) ( ( x ) | ( ( uint32_t ) 0x01U << ( position ) ) ) )

/**
 * @brief Macro for checking if a bit is set in a 4-byte unsigned int.
 *
 * @param[in] x The unsigned int to check.
 * @param[in] position Which bit to check.
 */
#define UINT32_CHECK_BIT( x, position ) \
    ( ( ( uint32_t ) ( x ) & ( ( uint32_t ) 0x01U << ( position ) ) ) == ( ( uint32_t ) 0x01U << ( position ) ) )

/**
 * @brief Per the MQTT spec, the largest "Remaining Length" of an MQTT
 * packet is this value, 256 MB.
 */
#define MQTT_MAX_REMAINING_LENGTH        ( 268435455U )

/**
 * @brief A value that represents an invalid remaining length.
 *
 * This value is greater than what is allowed by the MQTT specification.
 */
#define MQTT_REMAINING_LENGTH_INVALID    ( ( uint32_t ) MQTT_MAX_REMAINING_LENGTH + 1U )

/**
 * @brief Per the MQTT spec, the max packet size can be of max remaining length + 5 bytes.
 * Fixed header
 *    MQTT packet type nibble + MQTT flags nibble             1
 *    Maximum bytes used to encode the remaining length       4
 */
#define MQTT_MAX_PACKET_SIZE             ( MQTT_MAX_REMAINING_LENGTH + 5U )

/**
 * @brief A value that represents maximum value of UTF-8 encoded string.
 */
#define MQTT_MAX_UTF8_STR_LENGTH         ( ( uint32_t ) 65535 )

/**
 * @brief A value that represents the maximum value which can fit in a
 * variable byte integer.
 */
#define MAX_VARIABLE_LENGTH_INT_VALUE    ( ( uint32_t ) 268435455U )

/**
 * @brief A macro to check whether the uint32_t values will overflow when converted
 * to size_t.
 *
 * Evaluates to true when the value provided will overflow size_t variable. False otherwise.
 */
#if ( SIZE_MAX >= UINT32_MAX )
    #define CHECK_U32T_OVERFLOWS_SIZE_T( x )    false
#else
    #define CHECK_U32T_OVERFLOWS_SIZE_T( x )    ( ( x ) > SIZE_MAX )
#endif

/**
 * @brief A macro to check whether the size_t values will overflow when converted
 * to uint16_t which is used to represent MQTT UTF8 strings.
 *
 * Evaluates to true when the value provided will overflow 16-bit variable. False otherwise.
 */
#if ( 65535U >= SIZE_MAX )
    #define CHECK_SIZE_T_OVERFLOWS_16BIT( x )    false
#else
    #define CHECK_SIZE_T_OVERFLOWS_16BIT( x )    ( ( x ) > 65535U )
#endif

/**
 * @brief A macro to check whether the size_t values will overflow when converted
 * to uint32_t.
 *
 * Evaluates to true when the value provided will overflow 32-bit variable. False otherwise.
 */
#if ( 0xFFFFFFFFU >= SIZE_MAX )
    #define CHECK_SIZE_T_OVERFLOWS_32BIT( x )    false
#else
    #define CHECK_SIZE_T_OVERFLOWS_32BIT( x )    ( ( x ) > 0xFFFFFFFFU )
#endif

/**
 * @brief A macro to check whether the addition of two unsigned 32-bit numbers will overflow.
 *
 * Evaluates to true when the addition will overflow. False otherwise.
 */
#define ADDITION_WILL_OVERFLOW_U32( x, y ) \
    ( ( x ) > ( UINT32_MAX - ( y ) ) )

/**
 * @brief A macro to check whether the addition of two unsigned size_t numbers will overflow.
 *
 * Evaluates to true when the addition will overflow. False otherwise.
 */
#define ADDITION_WILL_OVERFLOW_SIZE_T( x, y ) \
    ( ( x ) > ( SIZE_MAX - ( y ) ) )

/**
 * @fn uint32_t variableLengthEncodedSize( uint32_t length );
 *
 * @brief Retrieve the size of the remaining length if it were to be encoded.
 *
 * @param[in] length The remaining length to be encoded.
 *
 * @note The length MUST be less than 268,435,455 as directed by the spec.
 *
 * @return The size of the remaining length if it were to be encoded.
 */

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this definition, this function is private.
 */
uint32_t variableLengthEncodedSize( uint32_t length );
/** @endcond */

/**
 * @fn uint8_t * encodeString( uint8_t * pDestination, const char * pSource, uint16_t sourceLength );
 *
 * @brief Encode a string whose size is at maximum 16 bits in length.
 *
 * @param[out] pDestination Destination buffer for the encoding.
 * @param[in] pSource The source string to encode.
 * @param[in] sourceLength The length of the source string to encode.
 *
 * @return A pointer to the end of the encoded string.
 */

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this definition, this function is private.
 */
uint8_t * encodeString( uint8_t * pDestination,
                        const char * pSource,
                        uint16_t sourceLength );
/** @endcond */

/**
 * @fn MQTTStatus_t decodeUserProp( const char ** pPropertyKey, size_t * pPropertyKeyLen, const char ** pPropertyValue, size_t * pPropertyValueLen, uint32_t * pPropertyLength, uint8_t ** pIndex );
 *
 * @brief Validate the length and decode a user property.
 *
 * @param[out] pPropertyKey To store the decoded key.
 * @param[out] pPropertyKeyLen To store the decoded key length.
 * @param[out] pPropertyValue To store the decoded value.
 * @param[out] pPropertyValueLen To store the decoded value length.
 * @param[in, out] pPropertyLength  Value of the remaining property length.
 * @param[in, out] pIndex Pointer to the current index of the buffer.
 *
 * @return #MQTTSuccess, #MQTTBadResponse
 **/

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this definition, this function is private.
 */
MQTTStatus_t decodeUserProp( const char ** pPropertyKey,
                             size_t * pPropertyKeyLen,
                             const char ** pPropertyValue,
                             size_t * pPropertyValueLen,
                             uint32_t * pPropertyLength,
                             uint8_t ** pIndex );
/** @endcond */

/**
 * @fn MQTTStatus_t decodeUint32t( uint32_t * pProperty, uint32_t * pPropertyLength, bool * pUsed, uint8_t ** pIndex );
 *
 * @brief Validate the length and decode a 4 byte value.
 *
 * @param[out] pProperty To store the decoded property.
 * @param[in, out] pPropertyLength  Value of the remaining property length.
 * @param[in, out] pUsed Whether the property is decoded before.
 * @param[in, out] pIndex Pointer to the current index of the buffer.
 *
 * @return #MQTTSuccess, #MQTTBadResponse
 **/

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this definition, this function is private.
 */
MQTTStatus_t decodeUint32t( uint32_t * pProperty,
                            uint32_t * pPropertyLength,
                            bool * pUsed,
                            uint8_t ** pIndex );
/** @endcond */

/**
 * @fn MQTTStatus_t decodeUint16t( uint16_t * pProperty, uint32_t * pPropertyLength, bool * pUsed, uint8_t ** pIndex );
 *
 * @brief Validate the length and decode a 2 byte value.
 *
 * @param[out] pProperty To store the decoded property.
 * @param[in, out] pPropertyLength  Value of the remaining property length.
 * @param[in, out] pUsed Whether the property is decoded before.
 * @param[in, out]  pIndex Pointer to the current index of the buffer.
 *
 * @return #MQTTSuccess, #MQTTBadResponse
 **/

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this definition, this function is private.
 */
MQTTStatus_t decodeUint16t( uint16_t * pProperty,
                            uint32_t * pPropertyLength,
                            bool * pUsed,
                            uint8_t ** pIndex );
/** @endcond */

/**
 * @fn MQTTStatus_t decodeUint8t( uint8_t * pProperty, uint32_t * pPropertyLength, bool * pUsed, uint8_t ** pIndex );
 *
 * @brief Validate the length and decode a 1 byte value.
 *
 * @param[out] pProperty To store the decoded property.
 * @param[in, out] pPropertyLength  Value of the remaining property length.
 * @param[in, out] pUsed Whether the property is decoded before.
 * @param[in, out]  pIndex Pointer to the current index of the buffer.
 *
 * @return #MQTTSuccess, #MQTTBadResponse
 **/

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this definition, this function is private.
 */
MQTTStatus_t decodeUint8t( uint8_t * pProperty,
                           uint32_t * pPropertyLength,
                           bool * pUsed,
                           uint8_t ** pIndex );
/** @endcond */

/**
 * @fn uint8_t * encodeVariableLength( uint8_t * pDestination, uint32_t length );
 *
 * @brief Encodes the remaining length of the packet using the variable length
 * encoding scheme provided in the MQTT 5.0 specification.
 *
 * @param[out] pDestination The destination buffer to store the encoded remaining
 * length.
 * @param[in] length The remaining length to encode.
 *
 * @return The location of the byte following the encoded value.
 */

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this definition, this function is private.
 */
uint8_t * encodeVariableLength( uint8_t * pDestination,
                                uint32_t length );
/** @endcond */

/**
 * @fn MQTTStatus_t decodeUtf8( const char ** pProperty, size_t * pLength, uint32_t * pPropertyLength, bool * pUsed, uint8_t ** pIndex );
 *
 * @brief Validate the length and decode a utf 8 string.
 *
 * @param[out] pProperty To store the decoded string.
 * @param[out] pLength  Size of the decoded utf-8 string.
 * @param[in, out] pPropertyLength  Value of the remaining property length.
 * @param[in, out] pUsed Whether the property is decoded before.
 * @param[in, out]  pIndex Pointer to the current index of the buffer.
 *
 * @return #MQTTSuccess, #MQTTBadResponse
 **/

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this definition, this function is private.
 */
MQTTStatus_t decodeUtf8( const char ** pProperty,
                         size_t * pLength,
                         uint32_t * pPropertyLength,
                         bool * pUsed,
                         uint8_t ** pIndex );
/** @endcond */

/**
 * @fn MQTTStatus_t decodeVariableLength( const uint8_t * pBuffer, size_t bufferLength, uint32_t * pLength );
 *
 * @brief Decodes the variable length by reading a single byte at a time.
 *
 * Uses the algorithm provided in the spec.
 *
 * @param[in] pBuffer Pointer to the buffer.
 * @param[in] bufferLength Length of the remaining buffer.
 * @param[out] pLength Decoded variable length
 *
 * @return #MQTTSuccess if variable length and paramters are valid else #MQTTBadResponse.
 */

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this definition, this function is private.
 */
MQTTStatus_t decodeVariableLength( const uint8_t * pBuffer,
                                   size_t bufferLength,
                                   uint32_t * pLength );
/** @endcond */

/**
 * @fn uint8_t * serializeAckFixed( uint8_t * pIndex, uint8_t packetType, uint16_t packetId, uint32_t remainingLength, MQTTSuccessFailReasonCode_t reasonCode );
 *
 * @brief Serialize the fixed size part of the ack packet header.
 *
 * @param[out] pIndex Pointer to the buffer where the header is to
 * be serialized.
 * @param[in] packetType Type of publish ack
 * @param[in] packetId Packed identifier of the ack packet.
 * @param[in] remainingLength Remaining length of the ack packet.
 * @param[in] reasonCode Reason code for the ack packet.
 *
 * @return A pointer to the end of the encoded string.
 */

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this definition, this function is private.
 */
uint8_t * serializeAckFixed( uint8_t * pIndex,
                             uint8_t packetType,
                             uint16_t packetId,
                             uint32_t remainingLength,
                             MQTTSuccessFailReasonCode_t reasonCode );
/** @endcond */

/**
 * @fn MQTTStatus_t decodeSubackPropertyLength( const uint8_t * pIndex, uint32_t remainingLength, uint32_t * subackPropertyLength );
 *
 * @brief Decodes the property length field in a SUBACK packet.
 *
 * @param[in] pIndex Pointer to the start of the properties in the SUBACK packet.
 * @param[in] remainingLength The remaining length of the MQTT packet being parsed, without Packet ID.
 * @param[out] subackPropertyLength The decoded property length including the size of its encoded representation.
 *
 * @return #MQTTSuccess if the property length is successfully decoded;
 *         #MQTTBadResponse if the decoded property length is greater than the remaining length.
 */

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this definition, this function is private.
 */
MQTTStatus_t decodeSubackPropertyLength( const uint8_t * pIndex,
                                         uint32_t remainingLength,
                                         uint32_t * subackPropertyLength );
/** @endcond */

/**
 * @fn uint8_t * serializeDisconnectFixed( uint8_t * pIndex, const MQTTSuccessFailReasonCode_t * pReasonCode, uint32_t remainingLength );
 *
 * @brief Serialize the fixed size part of the disconnect packet header.
 *
 * @param[out] pIndex Pointer to the buffer where the header is to be serialized.
 * @param[in] pReasonCode Reason code for the disconnect packet.
 * @param[in] remainingLength Remaining length of the disconnect packet.
 *
 * @return A pointer to the end of the encoded string.
 */

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this definition, this function is private.
 */
uint8_t * serializeDisconnectFixed( uint8_t * pIndex,
                                    const MQTTSuccessFailReasonCode_t * pReasonCode,
                                    uint32_t remainingLength );
/** @endcond */

/**
 * @fn uint8_t * serializeConnectFixedHeader( uint8_t * pIndex, const MQTTConnectInfo_t * pConnectInfo, const MQTTPublishInfo_t * pWillInfo, uint32_t remainingLength );
 * @brief Serialize the fixed part of the connect packet header.
 *
 * @param[out] pIndex Pointer to the buffer where the header is to
 * be serialized.
 * @param[in] pConnectInfo The connect information.
 * @param[in] pWillInfo The last will and testament information.
 * @param[in] remainingLength The remaining length of the packet to be
 * serialized.
 *
 * @return A pointer to the end of the encoded string.
 */

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this definition, this function is private.
 */
uint8_t * serializeConnectFixedHeader( uint8_t * pIndex,
                                       const MQTTConnectInfo_t * pConnectInfo,
                                       const MQTTPublishInfo_t * pWillInfo,
                                       uint32_t remainingLength );
/** @endcond */

/**
 * @fn  uint8_t * serializeSubscribeHeader( uint32_t remainingLength, uint8_t * pIndex, uint16_t packetId );
 * @brief Serialize the fixed part of the subscribe packet header.
 *
 * @param[in] remainingLength The remaining length of the packet to be
 * serialized.
 * @param[in] pIndex Pointer to the buffer where the header is to
 * be serialized.
 * @param[in] packetId The packet ID to be serialized.
 *
 * @return A pointer to the end of the encoded string.
 */

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this definition, this function is private.
 */
uint8_t * serializeSubscribeHeader( uint32_t remainingLength,
                                    uint8_t * pIndex,
                                    uint16_t packetId );
/** @endcond */

/**
 * @fn uint8_t * serializeUnsubscribeHeader( uint32_t remainingLength, uint8_t * pIndex, uint16_t packetId );
 * @brief Serialize the fixed part of the unsubscribe packet header.
 *
 * @param[in] remainingLength The remaining length of the packet to be
 * serialized.
 * @param[in] pIndex Pointer to the buffer where the header is to
 * be serialized.
 * @param[in] packetId The packet ID to be serialized.
 *
 * @return A pointer to the end of the encoded string.
 */

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this definition, this function is private.
 */
uint8_t * serializeUnsubscribeHeader( uint32_t remainingLength,
                                      uint8_t * pIndex,
                                      uint16_t packetId );
/** @endcond */

#endif /* ifndef CORE_MQTT_SERIALIZER_PRIVATE_H */

// === source/core_mqtt_serializer.c (verbatim from upstream) ===
/*
 * coreMQTT
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

/**
 * @file core_mqtt_serializer.c
 * @brief Implements the user-facing functions in core_mqtt_serializer.h.
 */
#include <string.h>
#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>




/* Include config defaults header to get default values of configs. */

/**
 * @brief Size of the fixed and variable header of a CONNECT packet.
 */
#define MQTT_PACKET_CONNECT_HEADER_SIZE             ( 10U )

/*
 * Positions of each flag in the first byte of an MQTT PUBLISH packet's
 * fixed header.
 */
#define MQTT_PUBLISH_FLAG_RETAIN                    ( 0 ) /**< @brief MQTT PUBLISH retain flag. */
#define MQTT_PUBLISH_FLAG_QOS1                      ( 1 ) /**< @brief MQTT PUBLISH QoS1 flag. */
#define MQTT_PUBLISH_FLAG_QOS2                      ( 2 ) /**< @brief MQTT PUBLISH QoS2 flag. */
#define MQTT_PUBLISH_FLAG_DUP                       ( 3 ) /**< @brief MQTT PUBLISH duplicate flag. */

/**
 * @brief A PINGREQ packet is always 2 bytes in size, defined by MQTT 5.0 spec.
 */
#define MQTT_PACKET_PINGREQ_SIZE                    ( 2U )

/*
 * Constants relating to CONNACK packets, defined by MQTT spec.
 */
#define MQTT_PACKET_CONNACK_SESSION_PRESENT_MASK    ( ( uint8_t ) 0x01U ) /**< @brief The "Session Present" bit is always the lowest bit. */

/**
 * @brief Minimum Length of PUBACK, PUBREC, PUBREL, PUBCOMP Packets
 */
#define MQTT_PACKET_SIMPLE_ACK_REMAINING_LENGTH     ( ( uint8_t ) 2 )

/**
 * @brief A PINGRESP packet always has a "Remaining length" of 0. */
#define MQTT_PACKET_PINGRESP_REMAINING_LENGTH       ( 0U )

/**
 * @brief Minimum number of bytes in the CONNACK Packet.
 * CONNECT Acknowledge Flags    0 + 1 = 1
 * CONNECT Reason Code            + 1 = 2
 * Property Length byte (min)     + 1 = 3
 */
#define MQTT_PACKET_CONNACK_MINIMUM_SIZE            ( 3U )

/*-----------------------------------------------------------*/

/**
 * @brief Serializes MQTT PUBLISH packet into the buffer provided.
 *
 * This function serializes MQTT PUBLISH packet into #MQTTFixedBuffer_t.pBuffer.
 * Copy of the payload into the buffer is done as part of the serialization
 * only if @p serializePayload is true.
 *
 * @param[in] pPublishInfo Publish information containing topic, QoS, payload and other
 * PUBLISH packet fields.
 * @param[in] pPublishProperties MQTT v5.0 properties for the PUBLISH packet. Can be NULL
 * if no properties are needed.
 * @param[in] remainingLength Remaining length of the PUBLISH packet.
 * @param[in] packetIdentifier Packet identifier of PUBLISH packet.
 * @param[in, out] pFixedBuffer Buffer to which PUBLISH packet will be
 * serialized.
 * @param[in] serializePayload Copy payload to the serialized buffer
 * only if true. Only PUBLISH header will be serialized if false.
 */
static void serializePublishCommon( const MQTTPublishInfo_t * pPublishInfo,
                                    const MQTTPropBuilder_t * pPublishProperties,
                                    uint32_t remainingLength,
                                    uint16_t packetIdentifier,
                                    const MQTTFixedBuffer_t * pFixedBuffer,
                                    bool serializePayload );

/**
 * @brief Calculates the packet size and remaining length of an MQTT
 * PUBLISH packet.
 *
 * @param[in] pPublishInfo MQTT PUBLISH packet parameters.
 * @param[out] pRemainingLength The Remaining Length of the MQTT PUBLISH packet.
 * @param[out] pPacketSize The total size of the MQTT PUBLISH packet.
 * @param[in] maxPacketSize Max packet size allowed by the server.
 * @param[in] publishPropertyLength Length of the optional properties in MQTT_PUBLISH
 *
 *
 * @return MQTTBadParameter if the packet would exceed the size allowed by the
 * MQTT spec; MQTTSuccess otherwise.
 */
static MQTTStatus_t calculatePublishPacketSize( const MQTTPublishInfo_t * pPublishInfo,
                                                uint32_t * pRemainingLength,
                                                uint32_t * pPacketSize,
                                                uint32_t maxPacketSize,
                                                uint32_t publishPropertyLength );

/**
 * @brief Calculates the packet size and remaining length of an MQTT
 * SUBSCRIBE or UNSUBSCRIBE packet.
 *
 * @param[in] pSubscriptionList List of MQTT subscription info.
 * @param[in] subscriptionCount The number of elements in pSubscriptionList.
 * @param[out] pRemainingLength The Remaining Length of the MQTT SUBSCRIBE or
 * UNSUBSCRIBE packet.
 * @param[out] pPacketSize The total size of the MQTT SUBSCRIBE or
 * MQTT UNSUBSCRIBE packet.
 * @param[in] subscribePropLen Length of the optional properties in MQTT_SUBSCRIBE or MQTT_UNSUBSCRIBE
 * @param[in] maxPacketSize Maximum Packet Size allowed by the broker
 * @param[in] subscriptionType #MQTT_TYPE_SUBSCRIBE or #MQTT_TYPE_UNSUBSCRIBE.
 *
 * @return MQTTBadParameter if the packet would exceed the size allowed by the
 * MQTT spec or a subscription is empty; MQTTSuccess otherwise.
 *
 */

static MQTTStatus_t calculateSubscriptionPacketSize( const MQTTSubscribeInfo_t * pSubscriptionList,
                                                     size_t subscriptionCount,
                                                     uint32_t * pRemainingLength,
                                                     uint32_t * pPacketSize,
                                                     uint32_t subscribePropLen,
                                                     uint32_t maxPacketSize,
                                                     MQTTSubscriptionType_t subscriptionType );

/**
 * @brief Validates parameters of #MQTT_SerializeSubscribe or
 * #MQTT_SerializeUnsubscribe.
 *
 * @param[in] pSubscriptionList List of MQTT subscription info.
 * @param[in] subscriptionCount The number of elements in pSubscriptionList.
 * @param[in] packetId Packet identifier.
 * @param[in] remainingLength Remaining length of the packet.
 * @param[in] pFixedBuffer Buffer for packet serialization.
 *
 * @return #MQTTNoMemory if pBuffer is too small to hold the MQTT packet;
 * #MQTTBadParameter if invalid parameters are passed;
 * #MQTTSuccess otherwise.
 */
static MQTTStatus_t validateSubscriptionSerializeParams( const MQTTSubscribeInfo_t * pSubscriptionList,
                                                         size_t subscriptionCount,
                                                         uint16_t packetId,
                                                         uint32_t remainingLength,
                                                         const MQTTFixedBuffer_t * pFixedBuffer );

/**
 * @brief Serialize an MQTT CONNECT packet in the given buffer.
 *
 * @param[in] pConnectInfo MQTT CONNECT packet parameters.
 * @param[in] pWillInfo Last Will and Testament. Pass NULL if not used.
 * @param[in] pConnectProperties MQTT CONNECT properties.
 * @param[in] pWillProperties MQTT Will properties.
 * @param[in] remainingLength Remaining Length of MQTT CONNECT packet.
 * @param[out] pFixedBuffer Buffer for packet serialization.
 */
static void serializeConnectPacket( const MQTTConnectInfo_t * pConnectInfo,
                                    const MQTTPublishInfo_t * pWillInfo,
                                    const MQTTPropBuilder_t * pConnectProperties,
                                    const MQTTPropBuilder_t * pWillProperties,
                                    uint32_t remainingLength,
                                    const MQTTFixedBuffer_t * pFixedBuffer );

/**
 * @brief Prints the appropriate message for the CONNACK response code if logs
 * are enabled.
 *
 * @param[in] responseCode MQTT standard CONNACK response code.
 */
static void logConnackResponse( uint8_t responseCode );

/**
 * @brief Retrieve the size of the remaining length if it were to be encoded.
 *
 * @param[in] length The remaining length to be encoded.
 *
 * @return The size of the remaining length if it were to be encoded.
 */
static uint32_t remainingLengthEncodedSize( uint32_t length );

/**
 * @brief Retrieves and decodes the Remaining Length from the network interface
 * by reading a single byte at a time.
 *
 * @param[in] recvFunc Network interface receive function.
 * @param[in] pNetworkContext Network interface context to the receive function.
 *
 * @return The Remaining Length of the incoming packet.
 */
static uint32_t getRemainingLength( TransportRecv_t recvFunc,
                                    NetworkContext_t * pNetworkContext );

/**
 * @brief Retrieves, decodes and stores the Remaining Length from the network
 * interface by reading a single byte at a time.
 *
 * @param[in] pBuffer The buffer holding the raw data to be processed
 * @param[in] pIndex Pointer to the index within the buffer to marking the end of raw data
 *            available.
 * @param[in] pIncomingPacket Structure used to hold the fields of the
 *            incoming packet.
 *
 * @return MQTTNeedMoreBytes is returned to show that the incoming
 *         packet is not yet fully received and decoded. Otherwise, MQTTSuccess
 *         shows that processing of the packet was successful.
 */
static MQTTStatus_t processRemainingLength( const uint8_t * pBuffer,
                                            const size_t * pIndex,
                                            MQTTPacketInfo_t * pIncomingPacket );

/**
 * @brief Check if an incoming packet type is valid.
 *
 * @param[in] packetType The packet type to check.
 *
 * @return `true` if the packet type is valid; `false` otherwise.
 */
static bool incomingPacketValid( uint8_t packetType );

/**
 * @brief Check the remaining length of an incoming PUBLISH packet against some
 * value for QoS 0, or for QoS 1 and 2.
 *
 * The remaining length for a QoS 1 and 2 packet will always be two greater than
 * for a QoS 0.
 *
 * @param[in] remainingLength Remaining length of the PUBLISH packet.
 * @param[in] qos The QoS of the PUBLISH.
 * @param[in] qos0Minimum Minimum possible remaining length for a QoS 0 PUBLISH.
 *
 * @return #MQTTSuccess or #MQTTBadResponse.
 */
static MQTTStatus_t checkPublishRemainingLength( uint32_t remainingLength,
                                                 MQTTQoS_t qos,
                                                 uint32_t qos0Minimum );

/**
 * @brief Process the flags of an incoming PUBLISH packet.
 *
 * @param[in] publishFlags Flags of an incoming PUBLISH.
 * @param[in, out] pPublishInfo Pointer to #MQTTPublishInfo_t struct where
 * output will be written.
 *
 * @return #MQTTSuccess or #MQTTBadResponse.
 */
static MQTTStatus_t processPublishFlags( uint8_t publishFlags,
                                         MQTTPublishInfo_t * pPublishInfo );

/**
 * @brief Deserialize an MQTT CONNACK packet.
 *
 * @param[out] pConnackProperties To store the deserialized connack properties.
 * @param[in]  pIncomingPacket #MQTTPacketInfo_t containing the buffer.
 * @param[out]  pSessionPresent Whether a previous session was present.
 * @param[out]  pPropBuffer MQTTPropBuilder_t to store the deserialized properties.
 *
 * @return #MQTTBadParameter, #MQTTBadResponse, or #MQTTSuccess.
 */
static MQTTStatus_t deserializeConnack( MQTTConnectionProperties_t * pConnackProperties,
                                        const MQTTPacketInfo_t * pIncomingPacket,
                                        bool * pSessionPresent,
                                        MQTTPropBuilder_t * pPropBuffer );

/**
 * @brief Decode the status bytes of a SUBACK packet to a #MQTTStatus_t.
 *
 * All known reason codes (including server rejections >= 0x80) are treated
 * as successful deserialization. The application can inspect individual
 * reason codes via #MQTTReasonCodeInfo_t in the event callback.
 *
 * @param[in] statusCount Number of status bytes in the SUBACK.
 * @param[in] pStatusStart The first status byte in the SUBACK.
 * @param[out] pReasonCodes The #MQTTReasonCodeInfo_t to store reason codes for each topic filter.
 * @return #MQTTSuccess or #MQTTBadResponse.
 */
static MQTTStatus_t readSubackStatus( size_t statusCount,
                                      const uint8_t * pStatusStart,
                                      MQTTReasonCodeInfo_t * pReasonCodes );

/**
 * @brief Deserialize an MQTT SUBACK / UNSUBACK packet.
 *
 * @param[in]  incomingPacket #MQTTPacketInfo_t containing the buffer.
 * @param[out]  pPacketId The packet ID obtained from the buffer.
 * @param[out]  pReasonCodes Struct to store reason code(s) from the acknowledgment packet.
 *                           Contains the success/failure status of the corresponding request.
 * @param[out]  pPropBuffer MQTTPropBuilder_t to store the deserialized properties.
 *
 * @return #MQTTBadParameter, #MQTTBadResponse, or #MQTTSuccess.
 */
static MQTTStatus_t deserializeSubUnsubAck( const MQTTPacketInfo_t * incomingPacket,
                                            uint16_t * pPacketId,
                                            MQTTReasonCodeInfo_t * pReasonCodes,
                                            MQTTPropBuilder_t * pPropBuffer );

/**
 * @brief Deserialize a PUBLISH packet received from the server.
 *
 * Converts the packet from a stream of bytes to an #MQTTPublishInfo_t and
 * extracts the packet identifier. Also prints out debug log messages about the
 * packet.
 *
 * @param[in] pIncomingPacket Pointer to an MQTT packet struct representing a
 * PUBLISH.
 * @param[out] pPacketId Packet identifier of the PUBLISH.
 * @param[out] pPublishInfo Pointer to #MQTTPublishInfo_t where output is
 * written.
 * @param[out] pPropBuffer Pointer to the property buffer.
 * @param[in] topicAliasMax Maximum allowed Topic Alias.
 *
 * @return #MQTTSuccess if PUBLISH is valid;
 * #MQTTBadResponse if the PUBLISH packet doesn't follow MQTT spec.
 */
static MQTTStatus_t deserializePublish( const MQTTPacketInfo_t * pIncomingPacket,
                                        uint16_t * pPacketId,
                                        MQTTPublishInfo_t * pPublishInfo,
                                        MQTTPropBuilder_t * pPropBuffer,
                                        uint16_t topicAliasMax );

/**
 * @brief Deserialize a PINGRESP packet.
 *
 * Converts the packet from a stream of bytes to an #MQTTStatus_t.
 *
 * @param[in] pPingresp Pointer to an MQTT packet struct representing a PINGRESP.
 *
 * @return #MQTTSuccess if PINGRESP is valid; #MQTTBadResponse if the PINGRESP
 * packet doesn't follow MQTT spec.
 */
static MQTTStatus_t deserializePingresp( const MQTTPacketInfo_t * pPingresp );

/**
 * @brief Validate the connack parameters.
 *
 * Converts the packet from a stream of bytes to an #MQTTStatus_t and extracts
 * the variable header without connack properties.
 *
 * @param[in] pIncomingPacket Pointer to an MQTT packet struct representing a incoming packet.
 * @param[out] pSessionPresent Whether a session is present or not.
 *
 *
 * @return #MQTTSuccess if connack  without connack properties is valid;
 * #MQTTServerRefused if the server refused the connection;
 * #MQTTBadResponse if the Connack packet doesn't follow MQTT spec.
 */
static MQTTStatus_t validateConnackParams( const MQTTPacketInfo_t * pIncomingPacket,
                                           bool * pSessionPresent );

/**
 * @brief Validate the length and decode the connack properties.
 *
 * @param[out] pConnackProperties To store the decoded property.
 * @param[in] length  Length of the properties.
 * @param[in] pIndex Pointer to the start of the properties.
 * @param[out] pPropBuffer Pointer to the property buffer.
 *
 * @return #MQTTSuccess, #MQTTBadResponse
 **/
static MQTTStatus_t deserializeConnackProperties( MQTTConnectionProperties_t * pConnackProperties,
                                                  uint32_t length,
                                                  uint8_t * pIndex,
                                                  MQTTPropBuilder_t * pPropBuffer );

/**
 * @brief Deserialize properties in the SUBACK packet received from the server.
 *
 * Converts the packet from a stream of bytes to an #MQTTStatus_t and extracts properties.
 *
 * @param[out] pPropBuffer Pointer to the property buffer.
 * @param[in] pIndex Pointer to the start of the properties.
 * @param[out] pSubackPropertyLength Pointer to the length of suback properties
 * @param[in] remainingLength Remaining length of the incoming packet.
 *
 * @return #MQTTSuccess if SUBACK is valid;
 * #MQTTBadResponse if SUBACK is invalid.
 *
 */
static MQTTStatus_t deserializeSubUnsubAckProperties( MQTTPropBuilder_t * pPropBuffer,
                                                      uint8_t * pIndex,
                                                      size_t * pSubackPropertyLength,
                                                      uint32_t remainingLength );

/**
 * @brief Deserialize an PUBACK, PUBREC, PUBREL, or PUBCOMP packet.
 *
 * Converts the packet from a stream of bytes to an #MQTTStatus_t and extracts
 * the packet identifier, reason code, properties.
 *
 * @param[in] pAck Pointer to the MQTT packet structure representing the packet.
 * @param[out] pPacketIdentifier Packet ID of the ack type packet.
 * @param[out] pReasonCode Structure to store reason code of the ack type packet.
 * @param[in] requestProblem To validate the packet.
 * @param[out] pPropBuffer Pointer to the property buffer.
 *
 * @return #MQTTSuccess, #MQTTBadResponse, #MQTTBadParameter.
 */
static MQTTStatus_t deserializePubAcks( const MQTTPacketInfo_t * pAck,
                                        uint16_t * pPacketIdentifier,
                                        MQTTReasonCodeInfo_t * pReasonCode,
                                        bool requestProblem,
                                        MQTTPropBuilder_t * pPropBuffer );

/**
 * @brief Validate the length and decode the publish ack properties.
 *
 * @param[out] pPropBuffer To store the decoded property.
 * @param[in] pIndex Pointer to the current index of the buffer.
 * @param[in] remainingLength Remaining length of properties in the incoming packet.
 *
 *
 * @return #MQTTSuccess, #MQTTBadResponse.
 **/
static MQTTStatus_t decodePubAckProperties( MQTTPropBuilder_t * pPropBuffer,
                                            uint8_t * pIndex,
                                            uint32_t remainingLength );

/**
 * @brief Prints the appropriate message for the PUBREL, PUBACK response code if logs
 * are enabled.
 *
 * @param[in] reasonCode MQTT Verion 5 standard PUBREL, PUBACK response code.
 * @param[in] packetIdentifier Packet id of the ack packet.
 *
 * @return #MQTTSuccess, #MQTTServerRefused and #MQTTBadResponse.
 */
static MQTTStatus_t logAckResponse( MQTTSuccessFailReasonCode_t reasonCode,
                                    uint16_t packetIdentifier );

/**
 * @brief Deserialize properties in the PUBLISH packet received from the server.
 *
 * Converts the packet from a stream of bytes to an #MQTTPublishInfo_t and
 * extracts properties.
 *
 * @param[out] pPublishInfo Pointer to #MQTTPublishInfo_t where output is
 * written.
 * @param[out] pPropBuffer Pointer to the property buffer.
 * @param[in] pIndex Pointer to the start of the properties.
 * @param[in] topicAliasMax Maximum allowed Topic Alias.
 * @param[in] remainingLength Remaining length of the incoming packet.
 *
 * @return #MQTTSuccess if PUBLISH is valid; #MQTTBadResponse
 * if the PUBLISH packet doesn't follow MQTT spec.
 */
static MQTTStatus_t deserializePublishProperties( MQTTPublishInfo_t * pPublishInfo,
                                                  MQTTPropBuilder_t * pPropBuffer,
                                                  uint8_t * pIndex,
                                                  uint16_t topicAliasMax,
                                                  uint32_t remainingLength );

/**
 * @brief Prints and validates the appropriate message for the Disconnect response code if logs
 * are enabled.
 *
 * @param[in] reasonCode MQTT Verion 5 standard DISCONNECT response code.
 * @param[in] incoming To differentiate between outgoing and incoming disconnect.
 *
 * @return #MQTTSuccess, #MQTTBadParameter and #MQTTBadResponse.
 */
static MQTTStatus_t validateDisconnectResponse( MQTTSuccessFailReasonCode_t reasonCode,
                                                bool incoming );

/**
 * @brief Validates the reason codes for the given ACK packet type.
 *
 * @param[in] ackPacketType ACK packet type for which the reason code is being added.
 * @param[in] reasonCode The reason code being added to the ACK packet type.
 *
 * @return #MQTTSuccess or #MQTTBadParameter.
 */
static MQTTStatus_t validateReasonCodeForAck( uint8_t ackPacketType,
                                              MQTTSuccessFailReasonCode_t reasonCode );

/**
 * @brief Validate if a reason code is valid for CONNACK packets.
 *
 * This function checks if the provided reason code is a valid CONNACK
 * reason code according to the MQTT v5 specification.
 *
 * @param[in] reasonCode The reason code to validate.
 *
 * @return #MQTTSuccess if the reason code is valid for CONNACK;
 * #MQTTServerRefused if the reason code indicates server refusal;
 * #MQTTBadResponse if the reason code is invalid.
 */
static inline MQTTStatus_t isValidConnackReasonCode( uint8_t reasonCode );

/**
 * @brief Validate properties in the DISCONNECT packet received from the server.
 *
 * @note Incoming properties are different than the ones the client can send.
 *
 * @param[in] pIndex Pointer to the start of the properties.
 * @param[in] disconnectPropertyLength Length of the properties in the DISCONNECT packet.
 *
 * @return #MQTTSuccess if DISCONNECT is valid;
 * #MQTTBadResponse if the DISCONNECT packet is invalid.
 */
static MQTTStatus_t validateIncomingDisconnectProperties( uint8_t * pIndex,
                                                          uint32_t disconnectPropertyLength );

/**
 * @brief Tracks which CONNACK properties have been seen during deserialization,
 *        used to detect duplicates.
 */
typedef struct ConnackSeenFlags
{
    bool sessionExpiry; /**< @brief Session Expiry Interval property seen. */
    bool receiveMax;    /**< @brief Receive Maximum property seen. */
    bool maxQos;        /**< @brief Maximum QoS property seen. */
    bool retain;        /**< @brief Retain Available property seen. */
    bool maxPacket;     /**< @brief Maximum Packet Size property seen. */
    bool clientId;      /**< @brief Assigned Client Identifier property seen. */
    bool topicAlias;    /**< @brief Topic Alias Maximum property seen. */
    bool wildcard;      /**< @brief Wildcard Subscription Available property seen. */
    bool subId;         /**< @brief Subscription Identifier Available property seen. */
    bool sharedSub;     /**< @brief Shared Subscription Available property seen. */
    bool keepAlive;     /**< @brief Server Keep Alive property seen. */
    bool responseInfo;  /**< @brief Response Information property seen. */
    bool serverRef;     /**< @brief Server Reference property seen. */
    bool authMethod;    /**< @brief Authentication Method property seen. */
    bool authData;      /**< @brief Authentication Data property seen. */
    bool reasonString;  /**< @brief Reason String property seen. */
} ConnackSeenFlags_t;

/**
 * @brief Decode and validate a single CONNACK property from the incoming packet.
 *
 * Reads one property from the variable header, validates its value, stores it
 * in the appropriate field of @p pConnackProperties, and sets the corresponding
 * bit in the property buffer's fieldSet if @p pPropBuffer is not NULL.
 *
 * @param[in] propertyId The MQTT property identifier byte.
 * @param[in,out] pConnackProperties Connection properties structure to populate.
 * @param[in,out] pPropertyLength Remaining bytes in the property section; decremented
 *                                as each property value is consumed.
 * @param[in,out] ppVariableHeader Pointer to the current read position in the packet
 *                                 buffer; advanced past the consumed property value.
 * @param[in,out] pPropBuffer Optional property builder to record which properties were
 *                            received. May be NULL.
 * @param[in,out] pSeen Duplicate-detection flags for each CONNACK property.
 *
 * @return #MQTTSuccess if the property was decoded and validated successfully.
 * @return #MQTTBadResponse if the property value is invalid (e.g., boolean out of range,
 *         zero where prohibited, response info sent without being requested) or if an
 *         unknown property ID is encountered.
 */
static MQTTStatus_t deserializeConnackProperty( uint8_t propertyId,
                                                MQTTConnectionProperties_t * pConnackProperties,
                                                uint32_t * pPropertyLength,
                                                uint8_t ** ppVariableHeader,
                                                MQTTPropBuilder_t * pPropBuffer,
                                                ConnackSeenFlags_t * pSeen );

/**
 * @brief Set a bit in pPropBuffer->fieldSet if pPropBuffer is not NULL.
 *
 * @param[in,out] pPropBuffer Property builder whose fieldSet will be updated.
 *                            If NULL, this function does nothing.
 * @param[in] bitPos Bit position to set in fieldSet.
 */
static void setConnackPropBit( MQTTPropBuilder_t * pPropBuffer,
                               uint8_t bitPos );

/**
 * @brief Validate that a uint8 property value is 0 or 1 (boolean).
 *
 * @param[in] value The decoded uint8 property value to validate.
 * @param[in] pPropName Human-readable property name used in the error log message.
 *
 * @return #MQTTSuccess if value is 0 or 1.
 * @return #MQTTBadResponse if value is greater than 1.
 */
static MQTTStatus_t validateBoolProp( uint8_t value,
                                      const char * pPropName );

/**
 * @brief Decode a uint8 boolean CONNACK property, validate it, and record it.
 *
 * Calls decodeUint8t to read the value, validateBoolProp to check it is 0 or 1,
 * and setConnackPropBit to mark the property as received in the property buffer.
 *
 * @param[out] pDest Destination to store the decoded uint8 value.
 * @param[in,out] pPropertyLength Remaining bytes in the property section; decremented
 *                                by the size of the decoded value.
 * @param[in,out] pSeen Duplicate-detection flag; set to true after first decode.
 * @param[in,out] ppIndex Current read position in the packet buffer; advanced past
 *                        the decoded value.
 * @param[in] pPropName Human-readable property name used in error log messages.
 * @param[in,out] pPropBuffer Optional property builder to record the property bit.
 *                            May be NULL.
 * @param[in] bitPos Bit position to set in pPropBuffer->fieldSet on success.
 *
 * @return #MQTTSuccess if the property was decoded and validated successfully.
 * @return #MQTTBadResponse if the value is not 0 or 1, or if decoding fails.
 */
static MQTTStatus_t decodeConnackBoolProp( uint8_t * pDest,
                                           uint32_t * pPropertyLength,
                                           bool * pSeen,
                                           uint8_t ** ppIndex,
                                           const char * pPropName,
                                           MQTTPropBuilder_t * pPropBuffer,
                                           uint8_t bitPos );

/*-----------------------------------------------------------*/

static MQTTStatus_t validateReasonCodeForAck( uint8_t ackPacketType,
                                              MQTTSuccessFailReasonCode_t reasonCode )
{
    MQTTStatus_t status = MQTTSuccess;

    switch( ackPacketType )
    {
        case MQTT_PACKET_TYPE_PUBACK:

            if( ( reasonCode != MQTT_REASON_PUBACK_SUCCESS ) &&
                ( reasonCode != MQTT_REASON_PUBACK_NO_MATCHING_SUBSCRIBERS ) &&
                ( reasonCode != MQTT_REASON_PUBACK_UNSPECIFIED_ERROR ) &&
                ( reasonCode != MQTT_REASON_PUBACK_IMPLEMENTATION_SPECIFIC_ERROR ) &&
                ( reasonCode != MQTT_REASON_PUBACK_NOT_AUTHORIZED ) &&
                ( reasonCode != MQTT_REASON_PUBACK_TOPIC_NAME_INVALID ) &&
                ( reasonCode != MQTT_REASON_PUBACK_PACKET_IDENTIFIER_IN_USE ) &&
                ( reasonCode != MQTT_REASON_PUBACK_QUOTA_EXCEEDED ) &&
                ( reasonCode != MQTT_REASON_PUBACK_PAYLOAD_FORMAT_INVALID ) )
            {
                LogError( ( "Invalid reason code for PUBACK." ) );
                status = MQTTBadParameter;
            }

            break;

        case MQTT_PACKET_TYPE_PUBREC:

            if( ( reasonCode != MQTT_REASON_PUBREC_SUCCESS ) &&
                ( reasonCode != MQTT_REASON_PUBREC_NO_MATCHING_SUBSCRIBERS ) &&
                ( reasonCode != MQTT_REASON_PUBREC_UNSPECIFIED_ERROR ) &&
                ( reasonCode != MQTT_REASON_PUBREC_IMPLEMENTATION_SPECIFIC_ERROR ) &&
                ( reasonCode != MQTT_REASON_PUBREC_NOT_AUTHORIZED ) &&
                ( reasonCode != MQTT_REASON_PUBREC_TOPIC_NAME_INVALID ) &&
                ( reasonCode != MQTT_REASON_PUBREC_PACKET_IDENTIFIER_IN_USE ) &&
                ( reasonCode != MQTT_REASON_PUBREC_QUOTA_EXCEEDED ) &&
                ( reasonCode != MQTT_REASON_PUBREC_PAYLOAD_FORMAT_INVALID ) )
            {
                LogError( ( "Invalid reason code for PUBREC." ) );
                status = MQTTBadParameter;
            }

            break;

        case MQTT_PACKET_TYPE_PUBREL:

            if( ( reasonCode != MQTT_REASON_PUBREL_SUCCESS ) &&
                ( reasonCode != MQTT_REASON_PUBREL_PACKET_IDENTIFIER_NOT_FOUND ) )
            {
                LogError( ( "Invalid reason code for PUBREL." ) );
                status = MQTTBadParameter;
            }

            break;

        case MQTT_PACKET_TYPE_PUBCOMP:

            if( ( reasonCode != MQTT_REASON_PUBCOMP_SUCCESS ) &&
                ( reasonCode != MQTT_REASON_PUBCOMP_PACKET_IDENTIFIER_NOT_FOUND ) )
            {
                LogError( ( "Invalid reason code for PUBCOMP." ) );
                status = MQTTBadParameter;
            }

            break;

        default:
            LogError( ( "Unknown ACK packet type: %" PRIu8 ".", ackPacketType ) );
            status = MQTTBadParameter;
            break;
    }

    return status;
}

/*-----------------------------------------------------------*/

static uint32_t remainingLengthEncodedSize( uint32_t length )
{
    uint32_t encodedSize;

    /* Determine how many bytes are needed to encode length.
     * The values below are taken from the MQTT 5.0 spec. */

    /* 1 byte is needed to encode lengths between 0 and 127. */
    if( length < 128U )
    {
        encodedSize = 1U;
    }
    /* 2 bytes are needed to encode lengths between 128 and 16,383. */
    else if( length < 16384U )
    {
        encodedSize = 2U;
    }
    /* 3 bytes are needed to encode lengths between 16,384 and 2,097,151. */
    else if( length < 2097152U )
    {
        encodedSize = 3U;
    }
    /* 4 bytes are needed to encode lengths between 2,097,152 and 268,435,455. */
    else
    {
        encodedSize = 4U;
    }

    LogDebug( ( "Encoded size for length %" PRIu32 " is %" PRIu32,
                length,
                encodedSize ) );

    return encodedSize;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t calculatePublishPacketSize( const MQTTPublishInfo_t * pPublishInfo,
                                                uint32_t * pRemainingLength,
                                                uint32_t * pPacketSize,
                                                uint32_t maxPacketSize,
                                                uint32_t publishPropertyLength )
{
    MQTTStatus_t status = MQTTSuccess;
    uint32_t packetSize = 0;
    uint32_t propertyAndPayloadLimit = 0;

    assert( pPublishInfo != NULL );
    assert( pRemainingLength != NULL );
    assert( pPacketSize != NULL );
    assert( !CHECK_SIZE_T_OVERFLOWS_16BIT( pPublishInfo->topicNameLength ) );
    assert( !CHECK_SIZE_T_OVERFLOWS_32BIT( pPublishInfo->payloadLength ) );

    /* The variable header of a PUBLISH packet always contains the topic name.
     * The first 2 bytes of UTF-8 string contains length of the string.
     */
    packetSize += ( uint32_t ) ( pPublishInfo->topicNameLength + sizeof( uint16_t ) );

    /* The variable header of a QoS 1 or 2 PUBLISH packet contains a 2-byte
     * packet identifier. */
    if( pPublishInfo->qos > MQTTQoS0 )
    {
        packetSize += 2U;
    }

    packetSize += variableLengthEncodedSize( publishPropertyLength );

    /* Calculate the maximum allowed size of the properties and payload combined for
     * the given parameters. */
    propertyAndPayloadLimit = MQTT_MAX_REMAINING_LENGTH - packetSize;

    if( publishPropertyLength > propertyAndPayloadLimit )
    {
        LogError( ( "PUBLISH properties length of %lu cannot exceed "
                    "%lu so as not to exceed the maximum "
                    "remaining length of MQTT 5.0 packet( %" PRIu32 " ).",
                    ( unsigned long ) publishPropertyLength,
                    ( unsigned long ) propertyAndPayloadLimit,
                    ( uint32_t ) MQTT_MAX_REMAINING_LENGTH ) );
        status = MQTTBadParameter;
    }
    else
    {
        packetSize += publishPropertyLength;
        propertyAndPayloadLimit -= publishPropertyLength;
    }

    if( status == MQTTSuccess )
    {
        if( pPublishInfo->payloadLength > propertyAndPayloadLimit )
        {
            LogError( ( "PUBLISH properties and payload combined length of %lu cannot exceed "
                        "%lu so as not to exceed the maximum "
                        "remaining length of MQTT 5.0 packet( %" PRIu32 " ).",
                        ( unsigned long ) ( pPublishInfo->payloadLength + publishPropertyLength ),
                        ( unsigned long ) ( propertyAndPayloadLimit + publishPropertyLength ),
                        ( uint32_t ) MQTT_MAX_REMAINING_LENGTH ) );
            status = MQTTBadParameter;
        }
        else
        {
            packetSize += ( uint32_t ) pPublishInfo->payloadLength;
        }
    }

    if( status == MQTTSuccess )
    {
        /* Set the "Remaining length" output parameter and calculate the full
         * size of the PUBLISH packet. */
        *pRemainingLength = packetSize;

        packetSize += 1U + variableLengthEncodedSize( packetSize );

        if( packetSize > maxPacketSize )
        {
            LogError( ( "Packet size is greater than the allowed maximum packet size." ) );
            status = MQTTBadParameter;
        }
        else
        {
            *pPacketSize = packetSize;
        }
    }

    LogDebug( ( "PUBLISH packet remaining length=%lu and packet size=%lu.",
                ( unsigned long ) *pRemainingLength,
                ( unsigned long ) *pPacketSize ) );

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t deserializePubAcks( const MQTTPacketInfo_t * pAck,
                                        uint16_t * pPacketIdentifier,
                                        MQTTReasonCodeInfo_t * pReasonCode,
                                        bool requestProblem,
                                        MQTTPropBuilder_t * pPropBuffer )
{
    MQTTStatus_t status = MQTTSuccess;
    uint8_t * pIndex;

    assert( pAck != NULL );
    assert( pPacketIdentifier != NULL );
    assert( pAck->pRemainingData != NULL );
    assert( !CHECK_U32T_OVERFLOWS_SIZE_T( pAck->remainingLength ) );

    pIndex = pAck->pRemainingData;

    if( pReasonCode == NULL )
    {
        LogError( ( "pReasonCode cannot be NULL." ) );
        status = MQTTBadParameter;
    }
    else if( pAck->remainingLength < 2U )
    {
        status = MQTTBadResponse;
    }
    else
    {
        /* Extract the packet identifier (third and fourth bytes) from ACK. */
        *pPacketIdentifier = UINT16_DECODE( pIndex );
        pIndex = &pIndex[ 2 ];

        LogDebug( ( "Packet identifier is %hu.",
                    ( unsigned short ) *pPacketIdentifier ) );

        /* Packet identifier cannot be 0. */
        if( *pPacketIdentifier == 0U )
        {
            LogError( ( "Packet identifier cannot be 0." ) );
            status = MQTTBadResponse;
        }
    }

    /* If reason code is success, server can choose to send the reason code or not. */
    if( ( status == MQTTSuccess ) && ( pAck->remainingLength > 2U ) )
    {
        pReasonCode->reasonCode = pIndex;
        pReasonCode->reasonCodeLength = 1U;
        pIndex++;
    }

    if( ( status == MQTTSuccess ) && ( pAck->remainingLength > 3U ) )
    {
        /* Protocol error to send user property and reason string if client has set request problem to false. */
        if( requestProblem == false )
        {
            LogError( ( "User property and reason string not expected in ACK packet when requestProblem is false." ) );
            status = MQTTBadResponse;
        }
        else
        {
            /* 3 bytes have been used up by the packet ID (2) and reason code (1). */
            status = decodePubAckProperties( pPropBuffer, pIndex, pAck->remainingLength - 3U );
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_SerializePublishHeaderWithoutTopic( const MQTTPublishInfo_t * pPublishInfo,
                                                      uint32_t remainingLength,
                                                      uint8_t * pBuffer,
                                                      size_t * headerSize )
{
    uint32_t headerLength;
    uint8_t * pIndex;
    MQTTStatus_t status = MQTTSuccess;

    /* The first byte of a PUBLISH packet contains the packet type and flags. */
    uint8_t publishFlags = MQTT_PACKET_TYPE_PUBLISH;

    if( pPublishInfo == NULL )
    {
        LogError( ( "pPublishInfo cannot be NULL." ) );
        status = MQTTBadParameter;
    }
    else if( pBuffer == NULL )
    {
        LogError( ( "pBuffer cannot be NULL." ) );
        status = MQTTBadParameter;
    }
    else if( remainingLength >= MQTT_REMAINING_LENGTH_INVALID )
    {
        LogError( ( "Remaining length must be less than 268435456." ) );
        status = MQTTBadParameter;
    }
    else if( headerSize == NULL )
    {
        LogError( ( "headerSize cannot be NULL." ) );
        status = MQTTBadParameter;
    }
    else
    {
        if( pPublishInfo->qos == MQTTQoS1 )
        {
            LogDebug( ( "Adding QoS as QoS1 in PUBLISH flags." ) );
            UINT8_SET_BIT( publishFlags, MQTT_PUBLISH_FLAG_QOS1 );
        }
        else if( pPublishInfo->qos == MQTTQoS2 )
        {
            LogDebug( ( "Adding QoS as QoS2 in PUBLISH flags." ) );
            UINT8_SET_BIT( publishFlags, MQTT_PUBLISH_FLAG_QOS2 );
        }
        else
        {
            /* Empty else MISRA 15.7 */
        }

        if( pPublishInfo->retain == true )
        {
            LogDebug( ( "Adding retain bit in PUBLISH flags." ) );
            UINT8_SET_BIT( publishFlags, MQTT_PUBLISH_FLAG_RETAIN );
        }

        if( pPublishInfo->dup == true )
        {
            LogDebug( ( "Adding dup bit in PUBLISH flags." ) );
            UINT8_SET_BIT( publishFlags, MQTT_PUBLISH_FLAG_DUP );
        }

        /* Get the start address of the buffer. */
        pIndex = pBuffer;

        /* Length of serialized packet = First byte
         *                               + Length of encoded remaining length
         *                               + Encoded topic length. */
        headerLength = 1U + remainingLengthEncodedSize( remainingLength ) + 2U;

        *pIndex = publishFlags;
        pIndex++;

        /* The "Remaining length" is encoded from the second byte. */
        pIndex = encodeVariableLength( pIndex, remainingLength );

        /* The first byte of a UTF-8 string is the high byte of the string length. */
        *pIndex = UINT16_HIGH_BYTE( pPublishInfo->topicNameLength );
        pIndex++;

        /* The second byte of a UTF-8 string is the low byte of the string length. */
        *pIndex = UINT16_LOW_BYTE( pPublishInfo->topicNameLength );
        pIndex++;

        /* We needn't check whether header length will overflow this cast as header length always < 8 (bytes). */
        *headerSize = ( size_t ) headerLength;
    }

    return status;
}

/*-----------------------------------------------------------*/

static void serializePublishCommon( const MQTTPublishInfo_t * pPublishInfo,
                                    const MQTTPropBuilder_t * pPublishProperties,
                                    uint32_t remainingLength,
                                    uint16_t packetIdentifier,
                                    const MQTTFixedBuffer_t * pFixedBuffer,
                                    bool serializePayload )
{
    uint8_t * pIndex = NULL;
    uint32_t propertyLength = 0U;
    /* The first byte of a PUBLISH packet contains the packet type and flags. */
    uint8_t publishFlags = MQTT_PACKET_TYPE_PUBLISH;

    assert( pPublishInfo != NULL );
    assert( pFixedBuffer != NULL );
    assert( pFixedBuffer->pBuffer != NULL );
    /* Packet Id should be non zero for Qos 1 and Qos 2. */
    assert( ( pPublishInfo->qos == MQTTQoS0 ) || ( packetIdentifier != 0U ) );
    /* Duplicate flag should be set only for Qos 1 or Qos 2. */
    assert( ( pPublishInfo->dup != true ) || ( pPublishInfo->qos != MQTTQoS0 ) );
    /* The topic name length must fit in 16-bits. */
    assert( !CHECK_SIZE_T_OVERFLOWS_16BIT( pPublishInfo->topicNameLength ) );

    /* Get the start address of the buffer. */
    pIndex = pFixedBuffer->pBuffer;

    if( ( pPublishProperties != NULL ) && ( pPublishProperties->pBuffer != NULL ) )
    {
        assert( !CHECK_SIZE_T_OVERFLOWS_32BIT( pPublishProperties->currentIndex ) );
        propertyLength = ( uint32_t ) pPublishProperties->currentIndex;
    }

    if( pPublishInfo->qos == MQTTQoS1 )
    {
        LogDebug( ( "Adding QoS as QoS1 in PUBLISH flags." ) );
        UINT8_SET_BIT( publishFlags, MQTT_PUBLISH_FLAG_QOS1 );
    }
    else if( pPublishInfo->qos == MQTTQoS2 )
    {
        LogDebug( ( "Adding QoS as QoS2 in PUBLISH flags." ) );
        UINT8_SET_BIT( publishFlags, MQTT_PUBLISH_FLAG_QOS2 );
    }
    else
    {
        /* No need to set any bits in a QoS0 packet. */
    }

    if( pPublishInfo->retain == true )
    {
        LogDebug( ( "Adding retain bit in PUBLISH flags." ) );
        UINT8_SET_BIT( publishFlags, MQTT_PUBLISH_FLAG_RETAIN );
    }

    if( pPublishInfo->dup == true )
    {
        LogDebug( ( "Adding dup bit in PUBLISH flags." ) );
        UINT8_SET_BIT( publishFlags, MQTT_PUBLISH_FLAG_DUP );
    }

    *pIndex = publishFlags;
    pIndex++;

    /* The "Remaining length" is encoded from the second byte. */
    pIndex = encodeVariableLength( pIndex, remainingLength );

    /* The topic name is placed after the "Remaining length". */
    pIndex = encodeString( pIndex,
                           pPublishInfo->pTopicName,
                           ( uint16_t ) pPublishInfo->topicNameLength );

    /* A packet identifier is required for QoS 1 and 2 messages. */
    if( pPublishInfo->qos > MQTTQoS0 )
    {
        LogDebug( ( "Adding packet Id in PUBLISH packet." ) );
        /* Place the packet identifier into the PUBLISH packet. */
        *pIndex = UINT16_HIGH_BYTE( packetIdentifier );
        pIndex[ 1U ] = UINT16_LOW_BYTE( packetIdentifier );
        pIndex = &pIndex[ 2U ];
    }

    /* Properties are added after packet identifier. */
    pIndex = encodeVariableLength( pIndex, propertyLength );

    if( propertyLength > 0U )
    {
        ( void ) memcpy( ( void * ) pIndex, ( const void * ) pPublishProperties->pBuffer, propertyLength );
        pIndex = &pIndex[ ( size_t ) propertyLength ];
    }

    /* The payload is placed after the properties.
     * Payload is copied over only if required by the flag serializePayload.
     * This will help reduce an unnecessary copy of the payload into the buffer.
     */
    if( ( pPublishInfo->payloadLength > 0U ) &&
        ( serializePayload == true ) )
    {
        LogDebug( ( "Copying PUBLISH payload of length =%lu to buffer",
                    ( unsigned long ) pPublishInfo->payloadLength ) );

        ( void ) memcpy( ( void * ) pIndex, ( const void * ) pPublishInfo->pPayload, pPublishInfo->payloadLength );
        /* Move the index to after the payload. */
        pIndex = &pIndex[ pPublishInfo->payloadLength ];
    }

    /* Ensure that the difference between the end and beginning of the buffer
     * is less than the buffer size. */
    assert( ( ( size_t ) ( pIndex - pFixedBuffer->pBuffer ) ) <= pFixedBuffer->size );
}

static uint32_t getRemainingLength( TransportRecv_t recvFunc,
                                    NetworkContext_t * pNetworkContext )
{
    uint32_t remainingLength = 0, multiplier = 1, bytesDecoded = 0, expectedSize = 0;
    uint8_t encodedByte = 0;
    int32_t bytesReceived = 0;

    /* This algorithm is copied from the MQTT v5.0 spec (same as v3.1.1). */
    do
    {
        if( multiplier > 2097152U ) /* 128 ^ 3 */
        {
            remainingLength = MQTT_REMAINING_LENGTH_INVALID;
        }
        else
        {
            bytesReceived = recvFunc( pNetworkContext, &encodedByte, 1U );

            if( bytesReceived == 1 )
            {
                /* Temporarily store the result before multiplying it with a multiplier. */
                uint8_t tempResult = encodedByte & 0x7FU;

                remainingLength += ( ( uint32_t ) tempResult ) * multiplier;
                multiplier *= 128U;
                bytesDecoded++;
            }
            else
            {
                remainingLength = MQTT_REMAINING_LENGTH_INVALID;
            }
        }

        if( remainingLength == MQTT_REMAINING_LENGTH_INVALID )
        {
            break;
        }
    } while( ( encodedByte & 0x80U ) != 0U );

    /* Check that the decoded remaining length conforms to the MQTT specification. */
    if( remainingLength != MQTT_REMAINING_LENGTH_INVALID )
    {
        expectedSize = remainingLengthEncodedSize( remainingLength );

        if( bytesDecoded != expectedSize )
        {
            remainingLength = MQTT_REMAINING_LENGTH_INVALID;
        }
    }

    return remainingLength;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t processRemainingLength( const uint8_t * pBuffer,
                                            const size_t * pIndex,
                                            MQTTPacketInfo_t * pIncomingPacket )
{
    uint32_t remainingLength = 0;
    uint32_t multiplier = 1;
    size_t bytesDecoded = 0;
    uint32_t expectedSize = 0;
    uint8_t encodedByte = 0;
    MQTTStatus_t status = MQTTSuccess;

    /* This algorithm is copied from the MQTT v5.0 spec. */
    do
    {
        if( multiplier > 2097152U ) /* 128 ^ 3 */
        {
            remainingLength = MQTT_REMAINING_LENGTH_INVALID;

            LogError( ( "Invalid remaining length in the packet.\n" ) );

            status = MQTTBadResponse;
        }
        else
        {
            if( *pIndex > ( bytesDecoded + 1U ) )
            {
                uint8_t tempResult;

                /* Get the next byte. It is at the next position after the bytes
                 * decoded till now since the header of one byte was read before. */
                encodedByte = pBuffer[ bytesDecoded + 1U ];

                /* Temporarily store the result before multiplying it with a multiplier. */
                tempResult = encodedByte & 0x7FU;

                remainingLength += ( ( uint32_t ) tempResult ) * multiplier;
                multiplier *= 128U;
                bytesDecoded++;
            }
            else
            {
                status = MQTTNeedMoreBytes;
            }
        }

        /* If the response is incorrect, or no more data is available, then
         * break out of the loop. */
        if( ( remainingLength == MQTT_REMAINING_LENGTH_INVALID ) ||
            ( status != MQTTSuccess ) )
        {
            break;
        }
    } while( ( encodedByte & 0x80U ) != 0U );

    if( status == MQTTSuccess )
    {
        /* Check that the decoded remaining length conforms to the MQTT specification. */
        expectedSize = variableLengthEncodedSize( remainingLength );

        if( bytesDecoded != ( ( size_t ) expectedSize ) )
        {
            LogError( ( "Expected and actual length of decoded bytes do not match.\n" ) );
            status = MQTTBadResponse;
        }
        else if( CHECK_U32T_OVERFLOWS_SIZE_T( remainingLength ) )
        {
            LogError( ( "Remaining length %" PRIu32
                        " will overflow when stored in pIncomingPacket->remainingLength "
                        "(type: size_t).", remainingLength ) );

            /* More details at: https://github.com/FreeRTOS/coreMQTT/blob/main/MISRA.md#rule-143 */
            /* coverity[misra_c_2012_rule_14_3_violation] */
            status = MQTTBadResponse;
        }
        else
        {
            pIncomingPacket->remainingLength = remainingLength;
            pIncomingPacket->headerLength = bytesDecoded + 1U;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static bool incomingPacketValid( uint8_t packetType )
{
    bool status = false;

    /* Check packet type. Mask out lower bits to ignore flags. */
    switch( packetType & 0xF0U )
    {
        /* Valid incoming packet types. */
        case MQTT_PACKET_TYPE_CONNACK:
        case MQTT_PACKET_TYPE_PUBLISH:
        case MQTT_PACKET_TYPE_PUBACK:
        case MQTT_PACKET_TYPE_PUBREC:
        case MQTT_PACKET_TYPE_PUBCOMP:
        case MQTT_PACKET_TYPE_SUBACK:
        case MQTT_PACKET_TYPE_UNSUBACK:
        case MQTT_PACKET_TYPE_PINGRESP:
        case MQTT_PACKET_TYPE_DISCONNECT:
        case MQTT_PACKET_TYPE_AUTH:
            status = true;
            break;

        case ( MQTT_PACKET_TYPE_PUBREL & 0xF0U ):

            /* The second bit of a PUBREL must be set. */
            if( ( packetType & 0x02U ) > 0U )
            {
                status = true;
            }

            break;

        /* Any other packet type is invalid. */
        default:
            LogWarn( ( "Incoming packet invalid: Packet type=%u.",
                       ( unsigned int ) packetType ) );
            break;
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t checkPublishRemainingLength( uint32_t remainingLength,
                                                 MQTTQoS_t qos,
                                                 uint32_t qos0Minimum )
{
    MQTTStatus_t status = MQTTSuccess;

    /* Sanity checks for "Remaining length". */
    if( qos == MQTTQoS0 )
    {
        /* Check that the "Remaining length" is greater than the minimum. */
        if( remainingLength < qos0Minimum )
        {
            LogError( ( "QoS 0 PUBLISH cannot have a remaining length less than %lu.",
                        ( unsigned long ) qos0Minimum ) );

            status = MQTTBadResponse;
        }
    }
    else
    {
        /* Check that the "Remaining length" is greater than the minimum. For
         * QoS 1 or 2, this will be two bytes greater than for QoS 0 due to the
         * packet identifier. */
        if( remainingLength < ( qos0Minimum + 2U ) )
        {
            LogError( ( "QoS 1 or 2 PUBLISH cannot have a remaining length less than %lu.",
                        ( unsigned long ) ( qos0Minimum + 2U ) ) );

            status = MQTTBadResponse;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t processPublishFlags( uint8_t publishFlags,
                                         MQTTPublishInfo_t * pPublishInfo )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pPublishInfo != NULL );

    /* Check for QoS 2. */
    if( UINT8_CHECK_BIT( publishFlags, MQTT_PUBLISH_FLAG_QOS2 ) )
    {
        /* PUBLISH packet is invalid if both QoS 1 and QoS 2 bits are set. */
        if( UINT8_CHECK_BIT( publishFlags, MQTT_PUBLISH_FLAG_QOS1 ) )
        {
            LogError( ( "Bad QoS: 3." ) );

            status = MQTTBadResponse;
        }
        else
        {
            pPublishInfo->qos = MQTTQoS2;
        }
    }
    /* Check for QoS 1. */
    else if( UINT8_CHECK_BIT( publishFlags, MQTT_PUBLISH_FLAG_QOS1 ) )
    {
        pPublishInfo->qos = MQTTQoS1;
    }
    /* If the PUBLISH isn't QoS 1 or 2, then it's QoS 0. */
    else
    {
        pPublishInfo->qos = MQTTQoS0;
    }

    if( status == MQTTSuccess )
    {
        LogDebug( ( "QoS is %d.", ( int ) pPublishInfo->qos ) );

        /* Parse the Retain bit. */
        pPublishInfo->retain = UINT8_CHECK_BIT( publishFlags, MQTT_PUBLISH_FLAG_RETAIN );

        LogDebug( ( "Retain bit is %d.", ( int ) pPublishInfo->retain ) );

        /* Parse the DUP bit. */
        pPublishInfo->dup = UINT8_CHECK_BIT( publishFlags, MQTT_PUBLISH_FLAG_DUP );

        LogDebug( ( "DUP bit is %d.", ( int ) pPublishInfo->dup ) );
    }

    return status;
}

/*-----------------------------------------------------------*/

static void logConnackResponse( uint8_t responseCode )
{
    /* Log an error based on the CONNACK response code. */
    switch( responseCode )
    {
        case ( uint8_t ) MQTT_REASON_CONNACK_SUCCESS:
            LogDebug( ( "Connection accepted." ) );
            break;

        case ( uint8_t ) MQTT_REASON_CONNACK_UNSPECIFIED_ERROR:
            LogError( ( "Connection refused: Unspecified error" ) );
            break;

        case ( uint8_t ) MQTT_REASON_CONNACK_MALFORMED_PACKET:
            LogError( ( "Connection refused: Malformed Packet." ) );
            break;

        case ( uint8_t ) MQTT_REASON_CONNACK_PROTOCOL_ERROR:
            LogError( ( "Connection refused: Protocol Error." ) );
            break;

        case ( uint8_t ) MQTT_REASON_CONNACK_IMPLEMENTATION_SPECIFIC_ERROR:
            LogError( ( "Connection refused: Implementation specific error." ) );
            break;

        case ( uint8_t ) MQTT_REASON_CONNACK_UNSUPPORTED_PROTOCOL_VERSION:
            LogError( ( "Connection refused: Unsupported Protocol Version." ) );
            break;

        case ( uint8_t ) MQTT_REASON_CONNACK_CLIENT_IDENTIFIER_NOT_VALID:
            LogError( ( "Connection refused: Client Identifier not valid." ) );
            break;

        case ( uint8_t ) MQTT_REASON_CONNACK_BAD_USER_NAME_OR_PASSWORD:
            LogError( ( "Connection refused: Bad User Name or Password." ) );
            break;

        case ( uint8_t ) MQTT_REASON_CONNACK_NOT_AUTHORIZED:
            LogError( ( "Connection refused: Not authorized." ) );
            break;

        case ( uint8_t ) MQTT_REASON_CONNACK_SERVER_UNAVAILABLE:
            LogError( ( "Connection refused: Server unavailable." ) );
            break;

        case ( uint8_t ) MQTT_REASON_CONNACK_SERVER_BUSY:
            LogError( ( "Connection refused: Server busy." ) );
            break;

        case ( uint8_t ) MQTT_REASON_CONNACK_BANNED:
            LogError( ( "Connection refused: Banned." ) );
            break;

        case ( uint8_t ) MQTT_REASON_CONNACK_BAD_AUTHENTICATION_METHOD:
            LogError( ( "Connection refused: Bad authentication method." ) );
            break;

        case ( uint8_t ) MQTT_REASON_CONNACK_TOPIC_NAME_INVALID:
            LogError( ( "Connection refused: Topic Name invalid." ) );
            break;

        case ( uint8_t ) MQTT_REASON_CONNACK_PACKET_TOO_LARGE:
            LogError( ( "Connection refused: Packet too large ." ) );
            break;

        case ( uint8_t ) MQTT_REASON_CONNACK_QUOTA_EXCEEDED:
            LogError( ( "Connection refused: Quota exceeded." ) );
            break;

        case ( uint8_t ) MQTT_REASON_CONNACK_PAYLOAD_FORMAT_INVALID:
            LogError( ( "Connection refused: Payload format invalid." ) );
            break;

        case ( uint8_t ) MQTT_REASON_CONNACK_RETAIN_NOT_SUPPORTED:
            LogError( ( "Connection refused: Retain not supported." ) );
            break;

        case ( uint8_t ) MQTT_REASON_CONNACK_QOS_NOT_SUPPORTED:
            LogError( ( "Connection refused: QoS not supported." ) );
            break;

        case ( uint8_t ) MQTT_REASON_CONNACK_USE_ANOTHER_SERVER:
            LogError( ( "Connection refused: Use another server." ) );
            break;

        case ( uint8_t ) MQTT_REASON_CONNACK_SERVER_MOVED:
            LogError( ( "Connection refused: Server moved." ) );
            break;

        case ( uint8_t ) MQTT_REASON_CONNACK_CONNECTION_RATE_EXCEEDED:
            LogError( ( "Connection refused: Connection rate exceeded." ) );
            break;

        /* This branch will never be reached as there the caller checks the value before-hand. */
        default:
            /* LCOV_EXCL_START */
            LogError( ( "Invalid reason code received." ) );
            assert( false );
            break;
            /* LCOV_EXCL_STOP */
    }
}

/*-----------------------------------------------------------*/

static inline MQTTStatus_t isValidConnackReasonCode( uint8_t reasonCode )
{
    MQTTStatus_t status;

    switch( reasonCode )
    {
        case ( uint8_t ) MQTT_REASON_CONNACK_SUCCESS:
        case ( uint8_t ) MQTT_REASON_CONNACK_UNSPECIFIED_ERROR:
        case ( uint8_t ) MQTT_REASON_CONNACK_MALFORMED_PACKET:
        case ( uint8_t ) MQTT_REASON_CONNACK_PROTOCOL_ERROR:
        case ( uint8_t ) MQTT_REASON_CONNACK_IMPLEMENTATION_SPECIFIC_ERROR:
        case ( uint8_t ) MQTT_REASON_CONNACK_UNSUPPORTED_PROTOCOL_VERSION:
        case ( uint8_t ) MQTT_REASON_CONNACK_CLIENT_IDENTIFIER_NOT_VALID:
        case ( uint8_t ) MQTT_REASON_CONNACK_BAD_USER_NAME_OR_PASSWORD:
        case ( uint8_t ) MQTT_REASON_CONNACK_NOT_AUTHORIZED:
        case ( uint8_t ) MQTT_REASON_CONNACK_SERVER_UNAVAILABLE:
        case ( uint8_t ) MQTT_REASON_CONNACK_SERVER_BUSY:
        case ( uint8_t ) MQTT_REASON_CONNACK_BANNED:
        case ( uint8_t ) MQTT_REASON_CONNACK_BAD_AUTHENTICATION_METHOD:
        case ( uint8_t ) MQTT_REASON_CONNACK_TOPIC_NAME_INVALID:
        case ( uint8_t ) MQTT_REASON_CONNACK_PACKET_TOO_LARGE:
        case ( uint8_t ) MQTT_REASON_CONNACK_QUOTA_EXCEEDED:
        case ( uint8_t ) MQTT_REASON_CONNACK_PAYLOAD_FORMAT_INVALID:
        case ( uint8_t ) MQTT_REASON_CONNACK_RETAIN_NOT_SUPPORTED:
        case ( uint8_t ) MQTT_REASON_CONNACK_QOS_NOT_SUPPORTED:
        case ( uint8_t ) MQTT_REASON_CONNACK_USE_ANOTHER_SERVER:
        case ( uint8_t ) MQTT_REASON_CONNACK_SERVER_MOVED:
        case ( uint8_t ) MQTT_REASON_CONNACK_CONNECTION_RATE_EXCEEDED:
            status = MQTTSuccess;
            break;

        default:
            LogError( ( "Invalid reason code received." ) );
            status = MQTTBadResponse;
            break;
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t validateConnackParams( const MQTTPacketInfo_t * pIncomingPacket,
                                           bool * pSessionPresent )
{
    MQTTStatus_t status = MQTTSuccess;
    const uint8_t * pRemainingData;
    uint8_t reasonCode;

    assert( pIncomingPacket != NULL );
    assert( pSessionPresent != NULL );
    assert( pIncomingPacket->pRemainingData != NULL );
    assert( pIncomingPacket->type == MQTT_PACKET_TYPE_CONNACK );

    /* Remaining Length of the CONNACK cannot be less than 3.
     * 1 byte for each of the following:
     * - Connect Acknowledge Flags
     * - Connect Reason Code
     * - Properties (0x00) indicating no trailing properties. */
    if( pIncomingPacket->remainingLength < MQTT_PACKET_CONNACK_MINIMUM_SIZE )
    {
        LogError( ( "Incomplete Connack received" ) );

        status = MQTTBadResponse;
    }

    if( status == MQTTSuccess )
    {
        pRemainingData = pIncomingPacket->pRemainingData;
        reasonCode = pRemainingData[ 1 ];

        /* Reserved bits in CONNACK must be 0. */
        if( ( pRemainingData[ 0 ] | 0x01U ) != 0x01U )
        {
            LogError( ( "Reserved bits in CONNACK not set to 0." ) );

            status = MQTTBadResponse;
        }
        else
        {
            /* Determine if the "Session Present" bit is set. This is the
             * lowest bit of the first byte of variable header. */
            if( ( pRemainingData[ 0 ] & MQTT_PACKET_CONNACK_SESSION_PRESENT_MASK ) ==
                MQTT_PACKET_CONNACK_SESSION_PRESENT_MASK )
            {
                LogDebug( ( "CONNACK session present bit set." ) );
                *pSessionPresent = true;

                /* MQTT 5 specifies that the fourth byte in CONNACK must be 0 if the
                 * "Session Present" bit is set. */
                if( reasonCode != 0U )
                {
                    LogError( ( "Session Present bit is set, but connect return code in CONNACK is %u (nonzero).",
                                ( unsigned int ) reasonCode ) );
                    status = MQTTBadResponse;
                }
            }
            else
            {
                LogDebug( ( "CONNACK session present bit not set." ) );
                *pSessionPresent = false;
            }
        }
    }

    if( status == MQTTSuccess )
    {
        if( isValidConnackReasonCode( reasonCode ) != MQTTSuccess )
        {
            status = MQTTBadResponse;
        }
        else
        {
            if( reasonCode != ( ( uint8_t ) MQTT_REASON_CONNACK_SUCCESS ) )
            {
                status = MQTTServerRefused;
            }

            logConnackResponse( reasonCode );
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t deserializeConnack( MQTTConnectionProperties_t * pConnackProperties,
                                        const MQTTPacketInfo_t * pIncomingPacket,
                                        bool * pSessionPresent,
                                        MQTTPropBuilder_t * pPropBuffer )
{
    MQTTStatus_t status = MQTTSuccess;
    uint32_t propertyLength = 0U;
    uint8_t * pVariableHeader = NULL;
    MQTTStatus_t statusCopy = MQTTSuccess;

    /* Validate the arguments. */
    status = validateConnackParams( pIncomingPacket, pSessionPresent );

    if( status == MQTTServerRefused )
    {
        statusCopy = status;
    }

    if( ( status == MQTTSuccess ) || ( status == MQTTServerRefused ) )
    {
        pVariableHeader = pIncomingPacket->pRemainingData;

        /* Skip over flags and reason code. */
        pVariableHeader = &pVariableHeader[ 2U ];

        /* More details at: https://github.com/FreeRTOS/coreMQTT/blob/main/MISRA.md#rule-108 */
        /* coverity[misra_c_2012_rule_10_8_violation] */
        status = decodeVariableLength( pVariableHeader, ( size_t ) ( pIncomingPacket->remainingLength - 2U ), &propertyLength );
    }

    /* Validate the packet size if max packet size is set. */
    if( status == MQTTSuccess )
    {
        /* Validate the remaining length. */
        if( ( pIncomingPacket->remainingLength ) != ( 2U + propertyLength + variableLengthEncodedSize( propertyLength ) ) )
        {
            LogError( ( "Invalid Remaining Length" ) );
            status = MQTTBadResponse;
        }
        /* Deserialize the connack properties. */
        else
        {
            status = deserializeConnackProperties( pConnackProperties, propertyLength, pVariableHeader, pPropBuffer );
        }
    }

    if( status == MQTTSuccess )
    {
        status = statusCopy;
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t calculateSubscriptionPacketSize( const MQTTSubscribeInfo_t * pSubscriptionList,
                                                     size_t subscriptionCount,
                                                     uint32_t * pRemainingLength,
                                                     uint32_t * pPacketSize,
                                                     uint32_t subscribePropLen,
                                                     uint32_t maxPacketSize,
                                                     MQTTSubscriptionType_t subscriptionType )
{
    uint32_t packetSize = 0U;
    size_t i;
    MQTTStatus_t status = MQTTSuccess;

    assert( pSubscriptionList != NULL );
    assert( pRemainingLength != NULL );
    assert( pPacketSize != NULL );
    assert( subscriptionCount != 0U );
    assert( subscribePropLen < MQTT_REMAINING_LENGTH_INVALID );

    /* 2 byte packet id. */
    packetSize += 2U;

    packetSize += subscribePropLen;
    packetSize += variableLengthEncodedSize( subscribePropLen );

    for( i = 0; i < subscriptionCount; i++ )
    {
        if( CHECK_SIZE_T_OVERFLOWS_16BIT( pSubscriptionList[ i ].topicFilterLength ) )
        {
            LogError( ( "Topic filter length must be less than 65536. Length is %" PRIu32, ( uint32_t ) pSubscriptionList[ i ].topicFilterLength ) );
            status = MQTTBadParameter;
        }
        else
        {
            /* We need not worry about overflow here as even when the subscribe property length is
             * maximum and topic filter is maximum, the addition will not overflow a uint32_t. */
            packetSize += ( uint32_t ) ( pSubscriptionList[ i ].topicFilterLength + 2U );

            if( packetSize >= MQTT_REMAINING_LENGTH_INVALID )
            {
                LogError( ( "Packet size must be smaller than 268435456" ) );
                status = MQTTBadParameter;
            }
            else if( subscriptionType == MQTT_TYPE_SUBSCRIBE )
            {
                packetSize += 1U;
            }
            else
            {
                /* Unsubscribe packet does not have an additional byte for QoS. */
            }
        }

        if( status != MQTTSuccess )
        {
            break;
        }
    }

    /* At this point, the "Remaining length" has been calculated. Return error
     * if the "Remaining length" exceeds what is allowed by MQTT 5. Otherwise,
     * set the output parameter. */
    if( ( status == MQTTSuccess ) && ( packetSize > MQTT_MAX_REMAINING_LENGTH ) )
    {
        LogError( ( "Subscribe packet size %" PRIu32 " exceeds 268435456.",
                    packetSize ) );
        status = MQTTBadParameter;
    }

    if( status == MQTTSuccess )
    {
        *pRemainingLength = packetSize;

        /* This is the total packet size which is the sum of:
         * Remaining Length +
         * Bytes required to encode the remaining length +
         * 1 byte MQTT header
         */
        packetSize += 1U + variableLengthEncodedSize( packetSize );
        *pPacketSize = packetSize;

        if( packetSize > maxPacketSize )
        {
            LogError( ( "Packet size is greater than the allowed maximum packet size." ) );
            status = MQTTBadParameter;
        }
    }

    LogDebug( ( "%s packet remaining length=%lu and packet size=%lu.",
                ( subscriptionType == MQTT_TYPE_SUBSCRIBE ) ? "SUBSCRIBE" : "UNSUBSCRIBE",
                ( unsigned long ) *pRemainingLength,
                ( unsigned long ) *pPacketSize ) );
    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t readSubackStatus( size_t statusCount,
                                      const uint8_t * pStatusStart,
                                      MQTTReasonCodeInfo_t * pReasonCodes )
{
    MQTTStatus_t status = MQTTSuccess;
    uint8_t subscriptionStatus = 0;
    size_t i = 0;

    assert( pStatusStart != NULL );

    for( i = 0; i < statusCount; i++ )
    {
        subscriptionStatus = pStatusStart[ i ];

        switch( subscriptionStatus )
        {
            case 0x00:
            case 0x01:
            case 0x02:
                LogDebug( ( "Topic Filter %lu accepted, max QoS %u.",
                            ( unsigned long ) i,
                            ( unsigned int ) subscriptionStatus ) );
                break;

            case 0x80:
                LogWarn( ( "Topic Filter Refused." ) );
                break;

            case 0x83:
                LogWarn( ( "Implementation specific error." ) );
                break;

            case 0x87:
                LogWarn( ( "Not authorized." ) );
                break;

            case 0x8F:
                LogWarn( ( "Topic Name Invalid." ) );
                break;

            case 0x91:
                LogWarn( ( "Packet Identifier In Use." ) );
                break;

            case 0x97:
                LogWarn( ( "Quota Exceeded." ) );
                break;

            case 0x9E:
                LogWarn( ( "Shared Subscriptions Not Supported." ) );
                break;

            case 0xA1:
                LogWarn( ( "Subscription Identifiers Not Supported." ) );
                break;

            case 0xA2:
                LogWarn( ( "Wildcard Subscriptions Not Supported." ) );
                break;

            default:
                LogError( ( "Bad Subscribe status %u.",
                            ( unsigned int ) subscriptionStatus ) );
                status = MQTTBadResponse;
                break;
        }

        if( status == MQTTBadResponse )
        {
            break;
        }
    }

    if( status == MQTTSuccess )
    {
        pReasonCodes->reasonCode = pStatusStart;
        pReasonCodes->reasonCodeLength = statusCount;
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t deserializeSubUnsubAck( const MQTTPacketInfo_t * incomingPacket,
                                            uint16_t * pPacketId,
                                            MQTTReasonCodeInfo_t * pReasonCodes,
                                            MQTTPropBuilder_t * pPropBuffer )
{
    MQTTStatus_t status = MQTTSuccess;
    uint8_t * pIndex = NULL;
    uint32_t remainingLength = 0U;
    size_t statusTotalBytes = 0U;
    const uint8_t * pStatusStart;
    size_t propertyLength = 0U;

    /* Validate input parameters using assert. */
    assert( incomingPacket != NULL );
    assert( pPacketId != NULL );
    assert( !CHECK_U32T_OVERFLOWS_SIZE_T( incomingPacket->remainingLength ) );

    pIndex = incomingPacket->pRemainingData;
    remainingLength = incomingPacket->remainingLength;

    if( pReasonCodes == NULL )
    {
        LogError( ( "pReasonCodes cannot be NULL for SUB/UNSUB ack packets." ) );
        status = MQTTBadParameter;
    }

    if( incomingPacket->remainingLength < 4U )
    {
        LogError( ( "Suback Packet Cannot have a remaining Length of less than 4." ) );
        status = MQTTBadResponse;
    }
    else
    {
        *pPacketId = UINT16_DECODE( pIndex );
        pIndex = &pIndex[ 2 ];
        LogDebug( ( "Packet Identifier is %hu.",
                    ( unsigned short ) *pPacketId ) );

        if( *pPacketId == 0U )
        {
            LogError( ( "Packet Id cannot be 0" ) );
            status = MQTTBadResponse;
        }
    }

    if( ( status == MQTTSuccess ) && ( incomingPacket->remainingLength >= 4U ) )
    {
        status = deserializeSubUnsubAckProperties( pPropBuffer,
                                                   pIndex,
                                                   &propertyLength,
                                                   incomingPacket->remainingLength );
    }

    if( status == MQTTSuccess )
    {
        uint32_t propertyLengthU32 = ( uint32_t ) propertyLength;
        /* Total number of bytes used by the properties - the encoded length + the actual properties. */
        /* More details at: https://github.com/FreeRTOS/coreMQTT/blob/main/MISRA.md#rule-108 */
        /* coverity[misra_c_2012_rule_10_8_violation] */
        size_t totalPropertiesLength = ( size_t ) ( propertyLengthU32 + variableLengthEncodedSize( propertyLengthU32 ) );

        /* Total bytes of status codes = length - packet ID - properties total length. */
        statusTotalBytes = remainingLength - sizeof( uint16_t ) - totalPropertiesLength;

        /* Status codes start just after the properties. */
        pStatusStart = &pIndex[ totalPropertiesLength ];
        status = readSubackStatus( statusTotalBytes, pStatusStart, pReasonCodes );
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t validateSubscriptionSerializeParams( const MQTTSubscribeInfo_t * pSubscriptionList,
                                                         size_t subscriptionCount,
                                                         uint16_t packetId,
                                                         uint32_t remainingLength,
                                                         const MQTTFixedBuffer_t * pFixedBuffer )
{
    MQTTStatus_t status = MQTTSuccess;
    size_t packetSize = 0;

    /* Validate all the parameters. */
    if( ( pFixedBuffer == NULL ) || ( pSubscriptionList == NULL ) )
    {
        LogError( ( "Argument cannot be NULL: pFixedBuffer=%p, "
                    "pSubscriptionList=%p.",
                    ( const void * ) pFixedBuffer,
                    ( const void * ) pSubscriptionList ) );
        status = MQTTBadParameter;
    }
    /* A buffer must be configured for serialization. */
    else if( pFixedBuffer->pBuffer == NULL )
    {
        LogError( ( "Argument cannot be NULL: pFixedBuffer->pBuffer is NULL." ) );
        status = MQTTBadParameter;
    }
    else if( subscriptionCount == 0U )
    {
        LogError( ( "Subscription count is 0." ) );
        status = MQTTBadParameter;
    }
    else if( packetId == 0U )
    {
        LogError( ( "Packet Id for subscription packet is 0." ) );
        status = MQTTBadParameter;
    }
    else if( remainingLength >= MQTT_REMAINING_LENGTH_INVALID )
    {
        LogError( ( "Remaining length must be less than 268435456." ) );
        status = MQTTBadParameter;
    }
    else
    {
        /* The serialized packet size = First byte
         * + length of encoded size of remaining length
         * + remaining length. */
        uint32_t serializedPacketSize = 1U + remainingLengthEncodedSize( remainingLength )
                                        + remainingLength;

        if( CHECK_U32T_OVERFLOWS_SIZE_T( serializedPacketSize ) )
        {
            LogError( ( "Serialized packet size will not fit in a size_t variable." ) );

            /* More details at: https://github.com/FreeRTOS/coreMQTT/blob/main/MISRA.md#rule-143 */
            /* coverity[misra_c_2012_rule_14_3_violation] */
            status = MQTTBadParameter;
        }
        else
        {
            packetSize = ( size_t ) serializedPacketSize;

            if( packetSize > pFixedBuffer->size )
            {
                LogError( ( "Buffer size of %lu is not sufficient to hold "
                            "serialized packet of size of %lu.",
                            ( unsigned long ) pFixedBuffer->size,
                            ( unsigned long ) packetSize ) );
                status = MQTTNoMemory;
            }
        }

        if( status == MQTTSuccess )
        {
            size_t it;

            for( it = 0; it < subscriptionCount; it++ )
            {
                /* Check whether the topic filter and the topic filter length are non-zero. */
                if( ( pSubscriptionList[ it ].pTopicFilter == NULL ) || ( pSubscriptionList[ it ].topicFilterLength == 0U ) )
                {
                    LogError( ( "Topic filter length must be non-zero and the topic filter must be non-NULL." ) );
                    status = MQTTBadParameter;
                }
                else if( CHECK_SIZE_T_OVERFLOWS_16BIT( pSubscriptionList[ it ].topicFilterLength ) )
                {
                    LogError( ( "Each topic filter must be less than 65535 characters long." ) );
                    status = MQTTBadParameter;
                }
                else
                {
                    /* Valid values. */
                }

                if( status != MQTTSuccess )
                {
                    break;
                }
            }
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t deserializePublish( const MQTTPacketInfo_t * pIncomingPacket,
                                        uint16_t * pPacketId,
                                        MQTTPublishInfo_t * pPublishInfo,
                                        MQTTPropBuilder_t * pPropBuffer,
                                        uint16_t topicAliasMax )
{
    MQTTStatus_t status = MQTTSuccess;
    const uint8_t * pPacketIdentifierHigh = NULL;
    uint8_t * pIndex = NULL;

    assert( pIncomingPacket != NULL );
    assert( pIncomingPacket->pRemainingData != NULL );
    assert( pPacketId != NULL );
    assert( pPublishInfo != NULL );

    pIndex = pIncomingPacket->pRemainingData;
    /* The flags are the lower 4 bits of the first byte in PUBLISH. */
    status = processPublishFlags( ( pIncomingPacket->type & 0x0FU ), pPublishInfo );

    if( status == MQTTSuccess )
    {
        /* Sanity checks for "Remaining length". A QoS 0 PUBLISH  must have a remaining
         * length of at least 4 to accommodate topic name length (2 bytes), topic name
         * (at least 1 byte) and, Property Length (at least 1 byte for 0 properties).
         * A QoS 1 or 2 PUBLISH must have a remaining length of at least 5 for the packet
         * identifier in addition to the topic name length and topic name. */
        status = checkPublishRemainingLength( pIncomingPacket->remainingLength,
                                              pPublishInfo->qos,
                                              4U );
    }

    if( status == MQTTSuccess )
    {
        /* Extract the topic name starting from the first byte of the variable header.
         * The topic name string starts at byte 3 in the variable header. */
        pPublishInfo->topicNameLength = UINT16_DECODE( pIndex );
        pIndex = &pIndex[ sizeof( uint16_t ) ];

        /* Sanity checks for topic name length and "Remaining length". The remaining
         * length must be at least as large as the variable length header:
         *   2 bytes to encode the Topic Length +
         *   length of the topic string +
         *   1 byte for the property length (when 0 properties).
         */
        status = checkPublishRemainingLength( pIncomingPacket->remainingLength,
                                              pPublishInfo->qos,
                                              2U + ( uint32_t ) pPublishInfo->topicNameLength + 1U );
    }

    if( status == MQTTSuccess )
    {
        /* Parse the topic. */
        pPublishInfo->pTopicName = ( char * ) pIndex;
        LogDebug( ( "Topic name: %hu.", ( unsigned short ) pPublishInfo->topicNameLength ) );

        /* Extract the packet identifier for QoS 1 or 2 PUBLISH packets. Packet
         * identifier starts immediately after the topic name. */
        pPacketIdentifierHigh = ( const uint8_t * ) ( &pPublishInfo->pTopicName[ pPublishInfo->topicNameLength ] );
        pIndex = &pIndex[ pPublishInfo->topicNameLength ];

        if( pPublishInfo->qos > MQTTQoS0 )
        {
            *pPacketId = UINT16_DECODE( pPacketIdentifierHigh );

            LogDebug( ( "Packet identifier %hu.",
                        ( unsigned short ) *pPacketId ) );

            /* Packet identifier cannot be 0. */
            if( *pPacketId == 0U )
            {
                LogError( ( "Packet identifier cannot be 0." ) );
                status = MQTTBadResponse;
            }

            if( status == MQTTSuccess )
            {
                pIndex = &pIndex[ sizeof( uint16_t ) ];
            }
        }
    }

    if( status == MQTTSuccess )
    {
        status = deserializePublishProperties( pPublishInfo,
                                               pPropBuffer,
                                               pIndex,
                                               topicAliasMax,
                                               pIncomingPacket->remainingLength );
    }

    if( status == MQTTSuccess )
    {
        /* Calculate the length of the payload. QoS 1 or 2 PUBLISH packets contain
         * a packet identifier, but QoS 0 PUBLISH packets do not. */
        uint32_t payloadLengthU32 = pIncomingPacket->remainingLength -
                                    ( ( ( uint32_t ) pPublishInfo->topicNameLength ) + 2U ) -
                                    ( ( ( uint32_t ) pPublishInfo->propertyLength ) + variableLengthEncodedSize( ( uint32_t ) pPublishInfo->propertyLength ) );

        pIndex = &pIndex[ ( size_t ) variableLengthEncodedSize( ( uint32_t ) pPublishInfo->propertyLength ) ];
        pIndex = &pIndex[ pPublishInfo->propertyLength ];

        if( CHECK_U32T_OVERFLOWS_SIZE_T( payloadLengthU32 ) )
        {
            LogError( ( "Payload length will not fit in size_t." ) );

            /* More details at: https://github.com/FreeRTOS/coreMQTT/blob/main/MISRA.md#rule-143 */
            /* coverity[misra_c_2012_rule_14_3_violation] */
            status = MQTTBadResponse;
        }
        else
        {
            pPublishInfo->payloadLength = payloadLengthU32;

            if( pPublishInfo->qos != MQTTQoS0 )
            {
                /* Two more bytes for the packet identifier. */
                pPublishInfo->payloadLength -= sizeof( uint16_t );
            }

            /* Set payload if it exists. */

            pPublishInfo->pPayload = ( pPublishInfo->payloadLength != 0U ) ? pIndex : NULL;

            LogDebug( ( "Payload length %lu.",
                        ( unsigned long ) pPublishInfo->payloadLength ) );
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t deserializePingresp( const MQTTPacketInfo_t * pPingresp )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pPingresp != NULL );

    /* Check the "Remaining length" (second byte) of the received PINGRESP is 0. */
    if( pPingresp->remainingLength != MQTT_PACKET_PINGRESP_REMAINING_LENGTH )
    {
        LogError( ( "PINGRESP does not have remaining length of %u.",
                    MQTT_PACKET_PINGRESP_REMAINING_LENGTH ) );

        status = MQTTBadResponse;
    }

    return status;
}

/*-----------------------------------------------------------*/

static void setConnackPropBit( MQTTPropBuilder_t * pPropBuffer,
                               uint8_t bitPos )
{
    if( pPropBuffer != NULL )
    {
        UINT32_SET_BIT( pPropBuffer->fieldSet, bitPos );
    }
}

/*-----------------------------------------------------------*/

static MQTTStatus_t validateBoolProp( uint8_t value,
                                      const char * pPropName )
{
    MQTTStatus_t status = MQTTSuccess;

    if( value > 1U )
    {
        LogError( ( "Server set %s to %u (not 0 or 1). Invalid response.", pPropName, value ) );
        status = MQTTBadResponse;
    }
    else
    {
        ( void ) pPropName;
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t decodeConnackBoolProp( uint8_t * pDest,
                                           uint32_t * pPropertyLength,
                                           bool * pSeen,
                                           uint8_t ** ppIndex,
                                           const char * pPropName,
                                           MQTTPropBuilder_t * pPropBuffer,
                                           uint8_t bitPos )
{
    MQTTStatus_t status = decodeUint8t( pDest, pPropertyLength, pSeen, ppIndex );

    if( status == MQTTSuccess )
    {
        status = validateBoolProp( *pDest, pPropName );
    }

    if( status == MQTTSuccess )
    {
        setConnackPropBit( pPropBuffer, bitPos );
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t deserializeConnackProperty( uint8_t propertyId,
                                                MQTTConnectionProperties_t * pConnackProperties,
                                                uint32_t * pPropertyLength,
                                                uint8_t ** ppVariableHeader,
                                                MQTTPropBuilder_t * pPropBuffer,
                                                ConnackSeenFlags_t * pSeen )
{
    MQTTStatus_t status = MQTTSuccess;
    const char * data;
    size_t dataLength;

    switch( propertyId )
    {
        case MQTT_SESSION_EXPIRY_ID:
            status = decodeUint32t( &pConnackProperties->sessionExpiry, pPropertyLength,
                                    &pSeen->sessionExpiry, ppVariableHeader );

            if( status == MQTTSuccess )
            {
                LogDebug( ( "Session expiry from server: %" PRIu32, pConnackProperties->sessionExpiry ) );
                setConnackPropBit( pPropBuffer, MQTT_SESSION_EXPIRY_INTERVAL_POS );
            }

            break;

        case MQTT_RECEIVE_MAX_ID:
            status = decodeUint16t( &pConnackProperties->serverReceiveMax, pPropertyLength,
                                    &pSeen->receiveMax, ppVariableHeader );

            if( ( status == MQTTSuccess ) && ( pConnackProperties->serverReceiveMax == 0U ) )
            {
                LogError( ( "Receive Maximum value set to 0 by the server." ) );
                status = MQTTBadResponse;
            }

            if( status == MQTTSuccess )
            {
                LogDebug( ( "Server receive maximum: %" PRIu16, pConnackProperties->serverReceiveMax ) );
                setConnackPropBit( pPropBuffer, MQTT_RECEIVE_MAXIMUM_POS );
            }

            break;

        case MQTT_MAX_QOS_ID:
            status = decodeConnackBoolProp( &pConnackProperties->serverMaxQos, pPropertyLength,
                                            &pSeen->maxQos, ppVariableHeader, "maximum QoS",
                                            pPropBuffer, MQTT_MAX_QOS_POS );

            if( status == MQTTSuccess )
            {
                LogDebug( ( "Server maximum QoS: %" PRIu8, pConnackProperties->serverMaxQos ) );
            }

            break;

        case MQTT_RETAIN_AVAILABLE_ID:
            status = decodeConnackBoolProp( &pConnackProperties->retainAvailable, pPropertyLength,
                                            &pSeen->retain, ppVariableHeader, "retain available",
                                            pPropBuffer, MQTT_RETAIN_AVAILABLE_POS );

            if( status == MQTTSuccess )
            {
                LogDebug( ( "Retain available: %" PRIu8, pConnackProperties->retainAvailable ) );
            }

            break;

        case MQTT_MAX_PACKET_SIZE_ID:
            status = decodeUint32t( &pConnackProperties->serverMaxPacketSize, pPropertyLength,
                                    &pSeen->maxPacket, ppVariableHeader );

            if( ( status == MQTTSuccess ) && ( pConnackProperties->serverMaxPacketSize == 0U ) )
            {
                LogError( ( "Server set maximum packet size to 0. Invalid response." ) );
                status = MQTTBadResponse;
            }

            if( status == MQTTSuccess )
            {
                LogDebug( ( "Server maximum packet size: %" PRIu32, pConnackProperties->serverMaxPacketSize ) );
                setConnackPropBit( pPropBuffer, MQTT_MAX_PACKET_SIZE_POS );
            }

            break;

        case MQTT_ASSIGNED_CLIENT_ID:
            status = decodeUtf8( &data, &dataLength, pPropertyLength, &pSeen->clientId, ppVariableHeader );

            if( status == MQTTSuccess )
            {
                LogDebug( ( "Assigned client ID: %.*s", ( int ) dataLength, data ) );
                setConnackPropBit( pPropBuffer, MQTT_ASSIGNED_CLIENT_ID_POS );
            }

            break;

        case MQTT_TOPIC_ALIAS_MAX_ID:
            status = decodeUint16t( &pConnackProperties->serverTopicAliasMax, pPropertyLength,
                                    &pSeen->topicAlias, ppVariableHeader );

            if( status == MQTTSuccess )
            {
                LogDebug( ( "Topic alias max ID: %" PRIu16, pConnackProperties->serverTopicAliasMax ) );
                setConnackPropBit( pPropBuffer, MQTT_TOPIC_ALIAS_MAX_POS );
            }

            break;

        case MQTT_REASON_STRING_ID:
            status = decodeUtf8( &data, &dataLength, pPropertyLength, &pSeen->reasonString, ppVariableHeader );

            if( status == MQTTSuccess )
            {
                LogInfo( ( "Reason string from server: %.*s", ( int ) dataLength, data ) );
                setConnackPropBit( pPropBuffer, MQTT_REASON_STRING_POS );
            }

            break;

        case MQTT_USER_PROPERTY_ID:
           {
               const char * key;
               const char * value;
               size_t keyLength;
               size_t valueLength;
               status = decodeUserProp( &key, &keyLength, &value, &valueLength, pPropertyLength, ppVariableHeader );

               if( status == MQTTSuccess )
               {
                   LogDebug( ( "User property: %.*s : %.*s", ( int ) keyLength, key, ( int ) valueLength, value ) );
                   setConnackPropBit( pPropBuffer, MQTT_USER_PROP_POS );
               }
           }
           break;

        case MQTT_WILDCARD_ID:
            status = decodeConnackBoolProp( &pConnackProperties->isWildcardAvailable, pPropertyLength,
                                            &pSeen->wildcard, ppVariableHeader, "wildcard",
                                            pPropBuffer, MQTT_WILDCARD_SUBSCRIPTION_AVAILABLE_POS );

            if( status == MQTTSuccess )
            {
                LogDebug( ( "Wildcard subscription available: %s",
                            pConnackProperties->isWildcardAvailable ? "Yes" : "No" ) );
            }

            break;

        case MQTT_SUB_AVAILABLE_ID:
            status = decodeConnackBoolProp( &pConnackProperties->isSubscriptionIdAvailable, pPropertyLength,
                                            &pSeen->subId, ppVariableHeader, "subscription ID availability",
                                            pPropBuffer, MQTT_SUBSCRIPTION_ID_AVAILABLE_POS );

            if( status == MQTTSuccess )
            {
                LogDebug( ( "Subscription ID available: %s",
                            pConnackProperties->isSubscriptionIdAvailable ? "Yes" : "No" ) );
            }

            break;

        case MQTT_SHARED_SUB_ID:
            status = decodeConnackBoolProp( &pConnackProperties->isSharedAvailable, pPropertyLength,
                                            &pSeen->sharedSub, ppVariableHeader, "shared sub availability",
                                            pPropBuffer, MQTT_SHARED_SUBSCRIPTION_AVAILABLE_POS );

            if( status == MQTTSuccess )
            {
                LogDebug( ( "Shared subscription available: %s",
                            pConnackProperties->isSharedAvailable ? "Yes" : "No" ) );
            }

            break;

        case MQTT_SERVER_KEEP_ALIVE_ID:
            status = decodeUint16t( &pConnackProperties->serverKeepAlive, pPropertyLength,
                                    &pSeen->keepAlive, ppVariableHeader );

            if( status == MQTTSuccess )
            {
                LogDebug( ( "Server keep alive: %d", ( int ) pConnackProperties->serverKeepAlive ) );
                setConnackPropBit( pPropBuffer, MQTT_SERVER_KEEP_ALIVE_POS );
            }

            break;

        case MQTT_RESPONSE_INFO_ID:
            status = decodeUtf8( &data, &dataLength, pPropertyLength, &pSeen->responseInfo, ppVariableHeader );

            if( ( status == MQTTSuccess ) && ( pConnackProperties->requestResponseInfo == false ) )
            {
                LogError( ( "Client did not request information still server sent it. Protocol error." ) );
                status = MQTTBadResponse;
            }

            if( status == MQTTSuccess )
            {
                LogDebug( ( "Response information: %.*s", ( int ) dataLength, data ) );
                setConnackPropBit( pPropBuffer, MQTT_RESPONSE_INFORMATION_POS );
            }

            break;

        case MQTT_SERVER_REF_ID:
            status = decodeUtf8( &data, &dataLength, pPropertyLength, &pSeen->serverRef, ppVariableHeader );

            if( status == MQTTSuccess )
            {
                LogDebug( ( "Server reference: %.*s", ( int ) dataLength, data ) );
                setConnackPropBit( pPropBuffer, MQTT_SERVER_REFERENCE_POS );
            }

            break;

        case MQTT_AUTH_METHOD_ID:
            status = decodeUtf8( &data, &dataLength, pPropertyLength, &pSeen->authMethod, ppVariableHeader );

            if( status == MQTTSuccess )
            {
                LogDebug( ( "Authentication method received: %.*s", ( int ) dataLength, data ) );
                setConnackPropBit( pPropBuffer, MQTT_AUTHENTICATION_METHOD_POS );
            }

            break;

        case MQTT_AUTH_DATA_ID:
            status = decodeUtf8( &data, &dataLength, pPropertyLength, &pSeen->authData, ppVariableHeader );

            if( status == MQTTSuccess )
            {
                LogDebug( ( "Auth data received: %.*s", ( int ) dataLength, data ) );
                setConnackPropBit( pPropBuffer, MQTT_AUTHENTICATION_DATA_POS );
            }

            break;

        default:
            status = MQTTBadResponse;
            break;
    }

    return status;
}

static MQTTStatus_t deserializeConnackProperties( MQTTConnectionProperties_t * pConnackProperties,
                                                  uint32_t length,
                                                  uint8_t * pIndex,
                                                  MQTTPropBuilder_t * pPropBuffer )
{
    MQTTStatus_t status = MQTTSuccess;
    uint8_t * pVariableHeader = pIndex;
    uint32_t propertyLength = length;

    ConnackSeenFlags_t seen = { false };

    pVariableHeader = &pVariableHeader[ variableLengthEncodedSize( propertyLength ) ];

    if( pPropBuffer != NULL )
    {
        pPropBuffer->pBuffer = pVariableHeader;
        pPropBuffer->bufferLength = propertyLength;
        pPropBuffer->currentIndex = propertyLength;
        pPropBuffer->fieldSet = 0U;
    }

    while( ( propertyLength > 0U ) && ( status == MQTTSuccess ) )
    {
        uint8_t propertyId = *pVariableHeader;

        pVariableHeader = &pVariableHeader[ 1 ];
        propertyLength -= 1U;

        status = deserializeConnackProperty( propertyId, pConnackProperties,
                                             &propertyLength, &pVariableHeader,
                                             pPropBuffer, &seen );
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t logAckResponse( MQTTSuccessFailReasonCode_t reasonCode,
                                    uint16_t packetIdentifier )
{
    MQTTStatus_t status = MQTTSuccess;

    switch( reasonCode )
    {
        case MQTT_REASON_PUBACK_SUCCESS: /* Also equivalent to MQTT_REASON_PUBREL_SUCCESS. */
            ( void ) packetIdentifier;
            break;

        case MQTT_REASON_PUBACK_NO_MATCHING_SUBSCRIBERS:
            LogDebug( ( "Publish accepted with packet id %hu: No matching subscribers.",
                        ( unsigned short ) packetIdentifier ) );
            break;

        case MQTT_REASON_PUBACK_UNSPECIFIED_ERROR:
            LogDebug( ( "Publish refused with packet id %hu: Connection rate exceeded.",
                        ( unsigned short ) packetIdentifier ) );
            break;

        case MQTT_REASON_PUBACK_IMPLEMENTATION_SPECIFIC_ERROR:
            LogDebug( ( "Publish refused with packet id %hu:  The PUBLISH is valid but the receiver is not willing to accept it.",
                        ( unsigned short ) packetIdentifier ) );
            break;

        case MQTT_REASON_PUBACK_NOT_AUTHORIZED:
            LogDebug( ( "Publish refused with packet id %hu: The PUBLISH is not authorized.",
                        ( unsigned short ) packetIdentifier ) );
            break;

        case MQTT_REASON_PUBACK_TOPIC_NAME_INVALID:
            LogDebug( ( "Publish refused with packet id %hu: Topic Name not accepted.",
                        ( unsigned short ) packetIdentifier ) );
            break;

        case MQTT_REASON_PUBACK_PACKET_IDENTIFIER_IN_USE:
            LogDebug( ( "Publish refused with packet id %hu: The Packet Identifier is already in use. ",
                        ( unsigned short ) packetIdentifier ) );
            break;

        case MQTT_REASON_PUBACK_QUOTA_EXCEEDED:
            LogDebug( ( "Publish refused with packet id %hu: Quota exceeded.",
                        ( unsigned short ) packetIdentifier ) );
            break;

        case MQTT_REASON_PUBACK_PAYLOAD_FORMAT_INVALID:
            LogDebug( ( "Publish refused with packet id %hu: Payload format indicator is invalid.",
                        ( unsigned short ) packetIdentifier ) );
            break;

        case MQTT_REASON_PUBREL_PACKET_IDENTIFIER_NOT_FOUND:
            LogError( ( "Publish refused with packet id %hu: Packet identifier invalid.",
                        ( unsigned short ) packetIdentifier ) );
            break;

        default:
            status = MQTTBadResponse;
            break;
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t deserializeSubUnsubAckProperties( MQTTPropBuilder_t * pPropBuffer,
                                                      uint8_t * pIndex,
                                                      size_t * pSubackPropertyLength,
                                                      uint32_t remainingLength )
{
    MQTTStatus_t status = MQTTSuccess;
    uint32_t propertyLength = 0U;
    uint8_t * pLocalIndex = pIndex;
    const char * pReasonString;
    size_t reasonStringLength;
    bool reasonString = false;

    assert( !CHECK_U32T_OVERFLOWS_SIZE_T( remainingLength ) );
    assert( remainingLength >= 2U );

    /* More details at: https://github.com/FreeRTOS/coreMQTT/blob/main/MISRA.md#rule-108 */
    /* coverity[misra_c_2012_rule_10_8_violation] */
    status = decodeVariableLength( pLocalIndex, ( size_t ) ( remainingLength - 2U ), &propertyLength );

    if( status == MQTTSuccess )
    {
        if( CHECK_U32T_OVERFLOWS_SIZE_T( propertyLength ) )
        {
            LogError( ( "Property length will overflow size_t variable." ) );

            /* More details at: https://github.com/FreeRTOS/coreMQTT/blob/main/MISRA.md#rule-143 */
            /* coverity[misra_c_2012_rule_14_3_violation] */
            status = MQTTBadParameter;
        }
        else
        {
            *pSubackPropertyLength = ( size_t ) propertyLength;
        }
    }

    if( status == MQTTSuccess )
    {
        uint32_t bytesForPropLen = variableLengthEncodedSize( propertyLength );

        pLocalIndex = &pLocalIndex[ ( size_t ) bytesForPropLen ];

        /* Remaining length should be at least big enough to hold the packet ID, the properties
         * and the encoded property length. */
        if( ( propertyLength + bytesForPropLen + 2U ) > remainingLength )
        {
            LogError( ( "Invalid property length. Goes beyond the packet bounds." ) );
            status = MQTTBadResponse;
        }
        else if( pPropBuffer != NULL )
        {
            pPropBuffer->bufferLength = propertyLength;
            pPropBuffer->pBuffer = pLocalIndex;
        }
        else
        {
            /* Nothing to do. No property buffer provided and no error. */
        }
    }

    while( ( propertyLength > 0U ) && ( status == MQTTSuccess ) )
    {
        uint8_t propertyId = *pLocalIndex;
        pLocalIndex = &pLocalIndex[ 1 ];
        propertyLength -= 1U;

        switch( propertyId )
        {
            case MQTT_REASON_STRING_ID:
                status = decodeUtf8( &pReasonString, &reasonStringLength, &propertyLength,
                                     &reasonString, &pLocalIndex );

                if( status == MQTTSuccess )
                {
                    if( pReasonString != NULL )
                    {
                        LogInfo( ( "SubAck reason string sent by server: %.*s",
                                   ( int ) reasonStringLength, pReasonString ) );
                    }
                }

                break;

            case MQTT_USER_PROPERTY_ID:
               {
                   const char * propertyKey;
                   size_t propertyKeyLen;
                   const char * propertyValue;
                   size_t propertyValueLen;
                   status = decodeUserProp( &propertyKey, &propertyKeyLen, &propertyValue,
                                            &propertyValueLen, &propertyLength, &pLocalIndex );
               }
               break;

            default:
                status = MQTTBadResponse;
                break;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static void serializeConnectPacket( const MQTTConnectInfo_t * pConnectInfo,
                                    const MQTTPublishInfo_t * pWillInfo,
                                    const MQTTPropBuilder_t * pConnectProperties,
                                    const MQTTPropBuilder_t * pWillProperties,
                                    uint32_t remainingLength,
                                    const MQTTFixedBuffer_t * pFixedBuffer )
{
    uint8_t * pIndex = NULL;
    uint32_t connectPropertyLength = 0U;
    uint32_t willPropertyLength = 0U;

    assert( pConnectInfo != NULL );
    assert( pFixedBuffer != NULL );
    assert( pFixedBuffer->pBuffer != NULL );
    assert( !CHECK_SIZE_T_OVERFLOWS_16BIT( pConnectInfo->clientIdentifierLength ) );
    assert( !CHECK_SIZE_T_OVERFLOWS_16BIT( pConnectInfo->userNameLength ) );
    assert( !CHECK_SIZE_T_OVERFLOWS_16BIT( pConnectInfo->passwordLength ) );

    if( pWillInfo != NULL )
    {
        assert( !CHECK_SIZE_T_OVERFLOWS_16BIT( pWillInfo->topicNameLength ) );
    }

    pIndex = pFixedBuffer->pBuffer;

    /* Serialize the header. */
    pIndex = serializeConnectFixedHeader( pIndex,
                                          pConnectInfo,
                                          pWillInfo,
                                          remainingLength );

    if( ( pConnectProperties != NULL ) && ( pConnectProperties->pBuffer != NULL ) )
    {
        assert( !CHECK_SIZE_T_OVERFLOWS_32BIT( pConnectProperties->currentIndex ) );
        connectPropertyLength = ( uint32_t ) pConnectProperties->currentIndex;
    }

    if( ( pWillProperties != NULL ) && ( pWillProperties->pBuffer != NULL ) )
    {
        assert( !CHECK_SIZE_T_OVERFLOWS_32BIT( pWillProperties->currentIndex ) );
        willPropertyLength = ( uint32_t ) pWillProperties->currentIndex;
    }

    /* Write the properties length into the CONNECT packet. */
    pIndex = encodeVariableLength( pIndex, connectPropertyLength );

    if( connectPropertyLength > 0U )
    {
        ( void ) memcpy( ( void * ) pIndex, ( const void * ) pConnectProperties->pBuffer, connectPropertyLength );
        pIndex = &pIndex[ ( size_t ) connectPropertyLength ];
    }

    /* Write the client identifier into the CONNECT packet. */
    pIndex = encodeString( pIndex,
                           pConnectInfo->pClientIdentifier,
                           ( uint16_t ) pConnectInfo->clientIdentifierLength );

    /* Write the will topic name and message into the CONNECT packet if provided. */
    if( pWillInfo != NULL )
    {
        pIndex = encodeVariableLength( pIndex, willPropertyLength );

        if( willPropertyLength > 0U )
        {
            ( void ) memcpy( ( void * ) pIndex, ( const void * ) pWillProperties->pBuffer, willPropertyLength );
            pIndex = &pIndex[ ( size_t ) willPropertyLength ];
        }

        pIndex = encodeString( pIndex,
                               pWillInfo->pTopicName,
                               ( uint16_t ) pWillInfo->topicNameLength );

        pIndex = encodeString( pIndex,
                               pWillInfo->pPayload,
                               ( uint16_t ) pWillInfo->payloadLength );
    }

    /* Encode the user name if provided. */
    if( pConnectInfo->pUserName != NULL )
    {
        pIndex = encodeString( pIndex, pConnectInfo->pUserName, ( uint16_t ) pConnectInfo->userNameLength );
    }

    /* Encode the password if provided. */
    if( pConnectInfo->pPassword != NULL )
    {
        pIndex = encodeString( pIndex, pConnectInfo->pPassword, ( uint16_t ) pConnectInfo->passwordLength );
    }

    LogDebug( ( "Length of serialized CONNECT packet is %lu.",
                ( ( unsigned long ) ( pIndex - pFixedBuffer->pBuffer ) ) ) );

    /* Ensure that the difference between the end and beginning of the buffer
     * is less than the buffer size. */
    assert( ( ( size_t ) ( pIndex - pFixedBuffer->pBuffer ) ) <= pFixedBuffer->size );
}

/*-----------------------------------------------------------*/

static MQTTStatus_t deserializePublishProperties( MQTTPublishInfo_t * pPublishInfo,
                                                  MQTTPropBuilder_t * pPropBuffer,
                                                  uint8_t * pIndex,
                                                  uint16_t topicAliasMax,
                                                  uint32_t remainingLength )
{
    MQTTStatus_t status = MQTTSuccess;
    uint32_t propertyLength = 0U;
    uint8_t * pLocalIndex = pIndex;
    uint32_t subscriptionId;
    uint32_t remainingLengthForProperties;
    bool contentType = false;
    bool messageExpiryInterval = false;
    bool responseTopic = false;
    bool topicAlias = false;
    bool payloadFormatIndicator = false;
    bool correlationData = false;
    uint16_t topicAliasVal;

    assert( !CHECK_SIZE_T_OVERFLOWS_16BIT( pPublishInfo->topicNameLength ) );
    assert( !CHECK_U32T_OVERFLOWS_SIZE_T( remainingLength ) );

    /* Decode Property Length. */
    remainingLengthForProperties = remainingLength;

    if( remainingLengthForProperties < ( pPublishInfo->topicNameLength + sizeof( uint16_t ) ) )
    {
        LogError( ( "Topic name length is greater than the remaining length." ) );
        status = MQTTBadParameter;
    }
    else
    {
        /* For QoS > 0, 2 byte packet ID is included. See whether the remaining length can accommodate that. */
        uint32_t qosEncodedLength = ( pPublishInfo->qos > MQTTQoS0 ) ? 2U : 0U;

        /* Topic is encoded as 2 bytes for the length and topic string. */
        remainingLengthForProperties -= ( ( uint32_t ) pPublishInfo->topicNameLength ) + 2U;

        if( remainingLengthForProperties < qosEncodedLength )
        {
            LogError( ( "Topic name length and QoS cannot fit in the remaining length." ) );
            status = MQTTBadParameter;
        }
        else
        {
            remainingLengthForProperties -= ( pPublishInfo->qos > MQTTQoS0 ) ? 2U : 0U;
        }
    }

    if( status == MQTTSuccess )
    {
        status = decodeVariableLength( pLocalIndex, ( size_t ) remainingLengthForProperties, &propertyLength );

        if( status == MQTTSuccess )
        {
            if( CHECK_U32T_OVERFLOWS_SIZE_T( propertyLength ) )
            {
                LogError( ( "Property length cannot fit in size_t." ) );

                /* More details at: https://github.com/FreeRTOS/coreMQTT/blob/main/MISRA.md#rule-143 */
                /* coverity[misra_c_2012_rule_14_3_violation] */
                status = MQTTBadResponse;
            }
            else
            {
                pPublishInfo->propertyLength = ( size_t ) propertyLength;
            }
        }
    }

    if( status == MQTTSuccess )
    {
        status = checkPublishRemainingLength( remainingLength,
                                              pPublishInfo->qos,
                                              ( ( uint32_t ) pPublishInfo->topicNameLength ) + 2U +
                                              propertyLength + variableLengthEncodedSize( propertyLength ) );
    }

    if( status == MQTTSuccess )
    {
        pLocalIndex = &pLocalIndex[ variableLengthEncodedSize( propertyLength ) ];
    }

    if( pPropBuffer != NULL )
    {
        pPropBuffer->pBuffer = pLocalIndex;
        pPropBuffer->bufferLength = propertyLength;
        pPropBuffer->currentIndex = propertyLength;
    }

    while( ( propertyLength > 0U ) && ( status == MQTTSuccess ) )
    {
        uint8_t propertyId = *pLocalIndex;
        pLocalIndex = &pLocalIndex[ 1 ];
        propertyLength -= 1U;

        switch( propertyId )
        {
            case MQTT_PAYLOAD_FORMAT_ID:
               {
                   uint8_t property;
                   status = decodeUint8t( &property, &propertyLength, &payloadFormatIndicator, &pLocalIndex );

                   if( status == MQTTSuccess )
                   {
                       /* Payload format must only be 0 or 1. */
                       if( property > 1U )
                       {
                           status = MQTTBadResponse;
                           LogError( ( "Payload Format Indicator is not 0x00. " ) );
                       }
                   }
               }
               break;

            case MQTT_TOPIC_ALIAS_ID:
                status = decodeUint16t( &topicAliasVal, &propertyLength, &topicAlias, &pLocalIndex );

                if( status == MQTTSuccess )
                {
                    if( topicAliasVal == 0U )
                    {
                        status = MQTTBadResponse;
                        LogError( ( "Topic Alias value of 0 is not permitted." ) );
                    }
                }

                break;

            case MQTT_RESPONSE_TOPIC_ID:
               {
                   const char * pProperty;
                   size_t length;
                   status = decodeUtf8( &pProperty, &length, &propertyLength, &responseTopic, &pLocalIndex );
               }
               break;

            case MQTT_CORRELATION_DATA_ID:
               {
                   const char * pProperty;
                   size_t length;
                   status = decodeUtf8( &pProperty, &length, &propertyLength, &correlationData, &pLocalIndex );
               }
               break;

            case MQTT_MSG_EXPIRY_ID:
               {
                   uint32_t property;
                   status = decodeUint32t( &property, &propertyLength, &messageExpiryInterval, &pLocalIndex );
               }
               break;

            case MQTT_CONTENT_TYPE_ID:
               {
                   const char * pProperty;
                   size_t length;
                   status = decodeUtf8( &pProperty, &length, &propertyLength, &contentType, &pLocalIndex );
               }
               break;

            case MQTT_SUBSCRIPTION_ID_ID:
                status = decodeVariableLength( pLocalIndex, ( size_t ) propertyLength, &subscriptionId );

                if( status == MQTTSuccess )
                {
                    pLocalIndex = &pLocalIndex[ variableLengthEncodedSize( subscriptionId ) ];
                    propertyLength -= variableLengthEncodedSize( subscriptionId );
                }

                break;

            case MQTT_USER_PROPERTY_ID:
               {
                   const char * pPropertyKey;
                   size_t propertyKeyLen;
                   const char * pPropertyValue;
                   size_t propertyValueLen;
                   status = decodeUserProp( &pPropertyKey,
                                            &propertyKeyLen,
                                            &pPropertyValue,
                                            &propertyValueLen,
                                            &propertyLength,
                                            &pLocalIndex );
               }
               break;

            default:
                status = MQTTBadResponse;
                break;
        }
    }

    if( ( status == MQTTSuccess ) && ( topicAlias == true ) )
    {
        if( topicAliasMax < topicAliasVal )
        {
            status = MQTTBadResponse;
            LogError( ( "Topic Alias greater than Topic Alias Max. " ) );
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t updateContextWithConnectProps( const MQTTPropBuilder_t * pPropBuilder,
                                            MQTTConnectionProperties_t * pConnectProperties )
{
    MQTTStatus_t status = MQTTSuccess;

    if( pPropBuilder == NULL )
    {
        LogError( ( "pPropBuilder cannot be NULL." ) );
        status = MQTTBadParameter;
    }
    else if( pPropBuilder->pBuffer == NULL )
    {
        LogError( ( "pPropBuilder->pBuffer cannot be NULL." ) );
        status = MQTTBadParameter;
    }
    else if( pConnectProperties == NULL )
    {
        LogError( ( "pConnectProperties cannot be NULL." ) );
        status = MQTTBadParameter;
    }
    else
    {
        bool maxPacket = false;
        bool sessionExpiry = false;
        bool receiveMax = false;
        bool topicAlias = false;
        uint32_t propertyLength = 0U;
        uint8_t * pIndex;

        assert( !CHECK_SIZE_T_OVERFLOWS_32BIT( pPropBuilder->currentIndex ) );
        assert( pPropBuilder->currentIndex < MQTT_REMAINING_LENGTH_INVALID );

        propertyLength = ( uint32_t ) pPropBuilder->currentIndex;
        pIndex = pPropBuilder->pBuffer; /* Pointer to the buffer */

        while( ( propertyLength > 0U ) && ( status == MQTTSuccess ) )
        {
            uint8_t propertyId = *pIndex;
            bool used = false;
            pIndex = &pIndex[ 1 ];
            propertyLength--;

            switch( propertyId )
            {
                case MQTT_SESSION_EXPIRY_ID:

                    /**
                     * This value shall get overwritten if the server sends a sessionExpiry
                     * in the CONNACK.
                     */
                    status = decodeUint32t( &pConnectProperties->sessionExpiry, &propertyLength,
                                            &sessionExpiry, &pIndex );
                    break;

                case MQTT_RECEIVE_MAX_ID:
                    status = decodeUint16t( &pConnectProperties->receiveMax, &propertyLength,
                                            &receiveMax, &pIndex );
                    break;

                case MQTT_MAX_PACKET_SIZE_ID:
                    status = decodeUint32t( &pConnectProperties->maxPacketSize, &propertyLength,
                                            &maxPacket, &pIndex );
                    break;

                case MQTT_TOPIC_ALIAS_MAX_ID:
                    status = decodeUint16t( &pConnectProperties->topicAliasMax, &propertyLength,
                                            &topicAlias, &pIndex );
                    break;

                case MQTT_REQUEST_PROBLEM_ID:
                case MQTT_REQUEST_RESPONSE_ID:
                   {
                       uint8_t property;
                       /* TODO: should this go in the context? */
                       status = decodeUint8t( &property, &propertyLength, &used, &pIndex );
                   }
                   break;

                case MQTT_AUTH_DATA_ID:
                case MQTT_AUTH_METHOD_ID:
                   {
                       const char * data;
                       size_t dataLength;
                       status = decodeUtf8( &data, &dataLength, &propertyLength, &used, &pIndex );
                   }
                   break;

                case MQTT_USER_PROPERTY_ID:
                   {
                       const char * key, * value;
                       size_t keyLength, valueLength;
                       status = decodeUserProp( &key,
                                                &keyLength,
                                                &value,
                                                &valueLength,
                                                &propertyLength,
                                                &pIndex );
                   }
                   break;

                default:
                    status = MQTTBadParameter;
                    break;
            }
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_GetConnectPacketSize( const MQTTConnectInfo_t * pConnectInfo,
                                        const MQTTPublishInfo_t * pWillInfo,
                                        const MQTTPropBuilder_t * pConnectProperties,
                                        const MQTTPropBuilder_t * pWillProperties,
                                        uint32_t * pRemainingLength,
                                        uint32_t * pPacketSize )
{
    MQTTStatus_t status = MQTTSuccess;
    uint32_t remainingLength;
    uint32_t propertyLength = 0U;
    uint32_t willPropertyLength = 0U;

    /* The CONNECT packet will always include a 10-byte variable header without connect properties. */
    uint32_t connectPacketSize = MQTT_PACKET_CONNECT_HEADER_SIZE;

    /* Validate arguments. */
    if( ( pConnectInfo == NULL ) || ( pRemainingLength == NULL ) ||
        ( pPacketSize == NULL ) )
    {
        LogError( ( "Argument cannot be NULL: pConnectInfo=%p, "
                    "pRemainingLength=%p, pPacketSize=%p.",
                    ( const void * ) pConnectInfo,
                    ( void * ) pRemainingLength,
                    ( void * ) pPacketSize ) );
        status = MQTTBadParameter;
    }
    else if( ( pConnectInfo->clientIdentifierLength == 0U ) !=
             ( ( pConnectInfo->pClientIdentifier == NULL ) || ( *( pConnectInfo->pClientIdentifier ) == '\0' ) ) )
    {
        LogError( ( "Client ID length and value mismatch." ) );
        status = MQTTBadParameter;
    }
    else if( CHECK_SIZE_T_OVERFLOWS_16BIT( pConnectInfo->clientIdentifierLength ) )
    {
        LogError( ( "Client ID length must be less than 65536 according to MQTT spec." ) );
        status = MQTTBadParameter;
    }
    else if( CHECK_SIZE_T_OVERFLOWS_16BIT( pConnectInfo->userNameLength ) )
    {
        LogError( ( "User name length must be less than 65536 according to MQTT spec." ) );
        status = MQTTBadParameter;
    }
    else if( CHECK_SIZE_T_OVERFLOWS_16BIT( pConnectInfo->passwordLength ) )
    {
        LogError( ( "Password length must be less than 65536 according to MQTT spec." ) );
        status = MQTTBadParameter;
    }
    else if( ( pWillInfo != NULL ) && CHECK_SIZE_T_OVERFLOWS_16BIT( pWillInfo->payloadLength ) )
    {
        /* The MQTTPublishInfo_t is reused for the will message. The payload
         * length for any other message could be larger than 65,535, but
         * the will message length is required to be represented in 2 bytes. */
        LogError( ( "The Will Message length must not exceed %d. "
                    "pWillInfo->payloadLength=%lu.",
                    UINT16_MAX,
                    ( unsigned long ) pWillInfo->payloadLength ) );
        status = MQTTBadParameter;
    }
    else if( ( pWillInfo != NULL ) && CHECK_SIZE_T_OVERFLOWS_16BIT( pWillInfo->topicNameLength ) )
    {
        LogError( ( "Will Topic name length must be less than 65536 according to MQTT spec." ) );
        status = MQTTBadParameter;
    }
    else
    {
        /* Do Nothing. */
    }

    if( ( status == MQTTSuccess ) && ( pConnectProperties != NULL ) && ( pConnectProperties->pBuffer != NULL ) )
    {
        /* The value must fit in a 32-bit variable all the while being small enough to
         * be properly encoded in a variable integer format. */
        if( CHECK_SIZE_T_OVERFLOWS_32BIT( pConnectProperties->currentIndex ) ||
            ( pConnectProperties->currentIndex > MQTT_MAX_REMAINING_LENGTH ) )
        {
            LogError( ( "Connect properties must be less than 268435456 "
                        "to be able to fit in a MQTT packet." ) );
            status = MQTTBadParameter;
        }
        else
        {
            propertyLength = ( uint32_t ) pConnectProperties->currentIndex;
        }
    }

    if( ( status == MQTTSuccess ) && ( pWillProperties != NULL ) && ( pWillProperties->pBuffer != NULL ) )
    {
        /* The value must fit in a 32-bit variable all the while being small enough to
         * be properly encoded in a variable integer format. */
        if( CHECK_SIZE_T_OVERFLOWS_32BIT( pWillProperties->currentIndex ) ||
            ( pWillProperties->currentIndex > MQTT_MAX_REMAINING_LENGTH ) )
        {
            LogError( ( "Will properties must be less than 268435456 "
                        "to be able to fit in a MQTT packet." ) );
            status = MQTTBadParameter;
        }
        else
        {
            willPropertyLength = ( uint32_t ) pWillProperties->currentIndex;
        }
    }

    if( status == MQTTSuccess )
    {
        /* Since property length, client ID length, will property length, will topic name length
         * and will payload length are ensured to be below their maximum value, connectPacketSize
         * will not overflow.
         * Max property length                     268435455
         * Max encoded prop length               +         4
         * Max client ID len (+2 byte len)       +     65535 + 2
         * Max will property length              + 268435455
         * Max will topic name len (+2 byte len) +     65535 + 2
         * Max will payload len (+2 byte len)    +     65535 + 2
         * Max username length (+2 byte len)     +     65535 + 2
         * Max password length (+2 byte len)     +     65535 + 2
         * Total                                 = 537198599 ( < UINT32_MAX ) */

        /* Add the length of the properties. */
        connectPacketSize += propertyLength;
        connectPacketSize += variableLengthEncodedSize( propertyLength );

        /* Add the length of the client identifier. */
        connectPacketSize += ( uint32_t ) ( pConnectInfo->clientIdentifierLength + sizeof( uint16_t ) );

        /* Add the lengths of the will message, topic name and properties if provided. */
        if( pWillInfo != NULL )
        {
            connectPacketSize += willPropertyLength;
            connectPacketSize += variableLengthEncodedSize( willPropertyLength );
            connectPacketSize += ( uint32_t ) ( pWillInfo->topicNameLength + sizeof( uint16_t ) +
                                                pWillInfo->payloadLength + sizeof( uint16_t ) );
        }

        /* Add the lengths of the user name and password if provided. */
        if( pConnectInfo->pUserName != NULL )
        {
            connectPacketSize += ( uint32_t ) ( pConnectInfo->userNameLength + sizeof( uint16_t ) );
        }

        if( pConnectInfo->pPassword != NULL )
        {
            connectPacketSize += ( uint32_t ) ( pConnectInfo->passwordLength + sizeof( uint16_t ) );
        }

        /* At this point, the "Remaining Length" field of the MQTT CONNECT packet has
         * been calculated. */
        remainingLength = connectPacketSize;

        if( remainingLength > MQTT_MAX_REMAINING_LENGTH )
        {
            LogError( ( "Packet remaining length is greater than maximum allowed." ) );
            status = MQTTBadParameter;
        }
        else
        {
            /* Calculate the full size of the MQTT CONNECT packet by adding the size of
             * the "Remaining Length" field plus 1 byte for the "Packet Type" field. */
            connectPacketSize += 1U + variableLengthEncodedSize( connectPacketSize );
        }
    }

    if( status == MQTTSuccess )
    {
        *pRemainingLength = remainingLength;
        *pPacketSize = connectPacketSize;

        LogDebug( ( "CONNECT packet remaining length=%lu and packet size=%lu.",
                    ( unsigned long ) *pRemainingLength,
                    ( unsigned long ) *pPacketSize ) );
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t decodePubAckProperties( MQTTPropBuilder_t * pPropBuffer,
                                            uint8_t * pIndex,
                                            uint32_t remainingLength )
{
    uint32_t propertyLength = 0U;
    MQTTStatus_t status = MQTTSuccess;
    uint8_t * pLocalIndex = pIndex;
    bool reasonString = false;

    assert( !CHECK_U32T_OVERFLOWS_SIZE_T( remainingLength ) );

    /* Decode the property length */
    status = decodeVariableLength( pLocalIndex, ( size_t ) remainingLength, &propertyLength );

    if( status == MQTTSuccess )
    {
        /* Validate the remaining length. Since properties are the last in the MQTT packet
         * the length which is remaining must be:
         *     Bytes taken to encode the property length +
         *     The actual length of the properties
         */
        if( remainingLength != ( propertyLength + variableLengthEncodedSize( propertyLength ) ) )
        {
            status = MQTTBadResponse;
        }
        else
        {
            pLocalIndex = &pLocalIndex[ variableLengthEncodedSize( propertyLength ) ];
        }
    }

    if( ( pPropBuffer != NULL ) && ( status == MQTTSuccess ) )
    {
        pPropBuffer->pBuffer = pLocalIndex;
        pPropBuffer->bufferLength = propertyLength;
    }

    while( ( propertyLength > 0U ) && ( status == MQTTSuccess ) )
    {
        /* Decode the property id. */
        uint8_t propertyId = *pLocalIndex;
        pLocalIndex = &pLocalIndex[ 1 ];
        propertyLength -= 1U;

        switch( propertyId )
        {
            case MQTT_REASON_STRING_ID:
               {
                   const char * pProperty;
                   size_t length;
                   status = decodeUtf8( &pProperty, &length, &propertyLength, &reasonString, &pLocalIndex );
                   break;
               }

            case MQTT_USER_PROPERTY_ID:
               {
                   const char * pPropertyKey;
                   size_t propertyKeyLen;
                   const char * pPropertyValue;
                   size_t propertyValueLen;
                   status = decodeUserProp( &pPropertyKey,
                                            &propertyKeyLen,
                                            &pPropertyValue,
                                            &propertyValueLen,
                                            &propertyLength,
                                            &pLocalIndex );
                   break;
               }

            default:
                status = MQTTBadResponse;
                break;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t validateDisconnectResponse( MQTTSuccessFailReasonCode_t reasonCode,
                                                bool incoming )
{
    MQTTStatus_t status;

    /* Validate the reason code. */
    /* coverity[misra_c_2012_rule_10_5_violation] */
    switch( reasonCode )
    {
        case MQTT_REASON_DISCONNECT_DISCONNECT_WITH_WILL_MESSAGE:

            if( incoming == true )
            {
                status = MQTTBadResponse;
            }
            else
            {
                status = MQTTSuccess;
            }

            break;

        case MQTT_REASON_DISCONNECT_NORMAL_DISCONNECTION:
        case MQTT_REASON_DISCONNECT_UNSPECIFIED_ERROR:
        case MQTT_REASON_DISCONNECT_MALFORMED_PACKET:
        case MQTT_REASON_DISCONNECT_PROTOCOL_ERROR:
        case MQTT_REASON_DISCONNECT_IMPLEMENTATION_SPECIFIC_ERROR:
        case MQTT_REASON_DISCONNECT_TOPIC_NAME_INVALID:
        case MQTT_REASON_DISCONNECT_RECEIVE_MAXIMUM_EXCEEDED:
        case MQTT_REASON_DISCONNECT_TOPIC_ALIAS_INVALID:
        case MQTT_REASON_DISCONNECT_PACKET_TOO_LARGE:
        case MQTT_REASON_DISCONNECT_MESSAGE_RATE_TOO_HIGH:
        case MQTT_REASON_DISCONNECT_QUOTA_EXCEEDED:
        case MQTT_REASON_DISCONNECT_ADMINISTRATIVE_ACTION:
        case MQTT_REASON_DISCONNECT_PAYLOAD_FORMAT_INVALID:
            status = MQTTSuccess;
            break;

        case MQTT_REASON_DISCONNECT_NOT_AUTHORIZED:
        case MQTT_REASON_DISCONNECT_SERVER_BUSY:
        case MQTT_REASON_DISCONNECT_SERVER_SHUTTING_DOWN:
        case MQTT_REASON_DISCONNECT_KEEP_ALIVE_TIMEOUT:
        case MQTT_REASON_DISCONNECT_SESSION_TAKEN_OVER:
        case MQTT_REASON_DISCONNECT_TOPIC_FILTER_INVALID:
        case MQTT_REASON_DISCONNECT_RETAIN_NOT_SUPPORTED:
        case MQTT_REASON_DISCONNECT_QOS_NOT_SUPPORTED:
        case MQTT_REASON_DISCONNECT_USE_ANOTHER_SERVER:
        case MQTT_REASON_DISCONNECT_SERVER_MOVED:
        case MQTT_REASON_DISCONNECT_MAXIMUM_CONNECT_TIME:
        case MQTT_REASON_DISCONNECT_SHARED_SUBSCRIPTIONS_NOT_SUPPORTED:
        case MQTT_REASON_DISCONNECT_WILDCARD_SUBSCRIPTIONS_NOT_SUPPORTED:
        case MQTT_REASON_DISCONNECT_SUBSCRIPTION_IDENTIFIERS_NOT_SUPPORTED:
        case MQTT_REASON_DISCONNECT_BAD_AUTHENTICATION_METHOD:

            if( incoming == true )
            {
                status = MQTTSuccess;
            }
            else
            {
                status = MQTTBadParameter;
            }

            break;

        default:
            status = MQTTBadResponse;
            break;
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_SerializeConnect( const MQTTConnectInfo_t * pConnectInfo,
                                    const MQTTPublishInfo_t * pWillInfo,
                                    const MQTTPropBuilder_t * pConnectProperties,
                                    const MQTTPropBuilder_t * pWillProperties,
                                    uint32_t remainingLength,
                                    const MQTTFixedBuffer_t * pFixedBuffer )
{
    MQTTStatus_t status = MQTTSuccess;
    uint32_t connectPacketSize = 0;

    /* Validate arguments. */
    if( ( pConnectInfo == NULL ) || ( pFixedBuffer == NULL ) )
    {
        LogError( ( "Argument cannot be NULL: pConnectInfo=%p, "
                    "pFixedBuffer=%p.",
                    ( const void * ) pConnectInfo,
                    ( const void * ) pFixedBuffer ) );
        status = MQTTBadParameter;
    }
    /* A buffer must be configured for serialization. */
    else if( pFixedBuffer->pBuffer == NULL )
    {
        LogError( ( "Argument cannot be NULL: pFixedBuffer->pBuffer is NULL." ) );
        status = MQTTBadParameter;
    }
    else if( ( pWillInfo != NULL ) && ( pWillInfo->pTopicName == NULL ) )
    {
        LogError( ( "pWillInfo->pTopicName cannot be NULL if Will is present." ) );
        status = MQTTBadParameter;
    }
    else if( CHECK_SIZE_T_OVERFLOWS_16BIT( pConnectInfo->clientIdentifierLength ) )
    {
        LogError( ( "clientIdentifierLength must be less than 65536 to fit in 16-bits." ) );
        status = MQTTBadParameter;
    }
    else if( CHECK_SIZE_T_OVERFLOWS_16BIT( pConnectInfo->userNameLength ) )
    {
        LogError( ( "userNameLength must be less than 65536 to fit in 16-bits." ) );
        status = MQTTBadParameter;
    }
    else if( CHECK_SIZE_T_OVERFLOWS_16BIT( pConnectInfo->passwordLength ) )
    {
        LogError( ( "passwordLength must be less than 65536 to fit in 16-bits." ) );
        status = MQTTBadParameter;
    }
    else if( ( pWillInfo != NULL ) && CHECK_SIZE_T_OVERFLOWS_16BIT( pWillInfo->topicNameLength ) )
    {
        LogError( ( "topicNameLength must be less than 65536 to fit in 16-bits." ) );
        status = MQTTBadParameter;
    }
    else
    {
        /* Calculate CONNECT packet size. Overflow in in this addition is not checked
         * because it is part of the API contract to call Mqtt_GetConnectPacketSize()
         * before this function. */
        connectPacketSize = remainingLength + variableLengthEncodedSize( remainingLength ) + 1U;

        /* Check that the full packet size fits within the given buffer. */
        if( connectPacketSize > pFixedBuffer->size )
        {
            LogError( ( "Buffer size of %lu is not sufficient to hold "
                        "serialized CONNECT packet of size of %lu.",
                        ( unsigned long ) pFixedBuffer->size,
                        ( unsigned long ) connectPacketSize ) );
            status = MQTTNoMemory;
        }
        else
        {
            serializeConnectPacket( pConnectInfo,
                                    pWillInfo,
                                    pConnectProperties,
                                    pWillProperties,
                                    remainingLength,
                                    pFixedBuffer );
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_GetSubscribePacketSize( const MQTTSubscribeInfo_t * pSubscriptionList,
                                          size_t subscriptionCount,
                                          const MQTTPropBuilder_t * pSubscribeProperties,
                                          uint32_t * pRemainingLength,
                                          uint32_t * pPacketSize,
                                          uint32_t maxPacketSize )
{
    MQTTStatus_t status = MQTTSuccess;
    uint32_t propertyLength = 0U;

    if( pSubscriptionList == NULL )
    {
        LogError( ( "Argument cannot be null : SubscriptionList" ) );
        status = MQTTBadParameter;
    }
    else if( subscriptionCount == 0U )
    {
        LogError( ( "Subscription count cannot be 0" ) );
        status = MQTTBadParameter;
    }
    else if( maxPacketSize == 0U )
    {
        LogError( ( "Max Packet size cannot be 0" ) );
        status = MQTTBadParameter;
    }
    else if( pRemainingLength == NULL )
    {
        LogError( ( "Pointer to remaining length cannot be NULL." ) );
        status = MQTTBadParameter;
    }
    else
    {
        if( ( pSubscribeProperties != NULL ) && ( pSubscribeProperties->pBuffer != NULL ) )
        {
            /* The value must fit in a 32-bit variable all the while being small enough to
             * be properly encoded in a variable integer format. */
            if( CHECK_SIZE_T_OVERFLOWS_32BIT( pSubscribeProperties->currentIndex ) ||
                ( pSubscribeProperties->currentIndex > MQTT_MAX_REMAINING_LENGTH ) )
            {
                LogError( ( "Subscription properties must be less than 268435456 "
                            "to be able to fit in a MQTT packet." ) );
                status = MQTTBadParameter;
            }
            else
            {
                propertyLength = ( uint32_t ) pSubscribeProperties->currentIndex;
            }
        }

        if( status == MQTTSuccess )
        {
            status = calculateSubscriptionPacketSize( pSubscriptionList, subscriptionCount,
                                                      pRemainingLength, pPacketSize, propertyLength,
                                                      maxPacketSize, MQTT_TYPE_SUBSCRIBE );
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_SerializeSubscribe( const MQTTSubscribeInfo_t * pSubscriptionList,
                                      size_t subscriptionCount,
                                      const MQTTPropBuilder_t * pSubscribeProperties,
                                      uint16_t packetId,
                                      uint32_t remainingLength,
                                      const MQTTFixedBuffer_t * pFixedBuffer )
{
    size_t i = 0;
    uint8_t * pIndex = NULL;
    uint32_t propertyLength = 0U;
    MQTTStatus_t status = MQTTSuccess;

    if( ( pSubscribeProperties != NULL ) && ( pSubscribeProperties->pBuffer != NULL ) )
    {
        if( CHECK_SIZE_T_OVERFLOWS_32BIT( pSubscribeProperties->currentIndex ) ||
            ( pSubscribeProperties->currentIndex >= MQTT_REMAINING_LENGTH_INVALID ) )
        {
            LogError( ( "Subscribe properties cannot have a length more than 268435455." ) );
            status = MQTTBadParameter;
        }
        else
        {
            propertyLength = ( uint32_t ) pSubscribeProperties->currentIndex;
        }
    }

    if( status == MQTTSuccess )
    {
        /* Validate all the parameters. */
        status = validateSubscriptionSerializeParams( pSubscriptionList,
                                                      subscriptionCount,
                                                      packetId,
                                                      remainingLength,
                                                      pFixedBuffer );
    }

    if( status == MQTTSuccess )
    {
        pIndex = pFixedBuffer->pBuffer;

        pIndex = serializeSubscribeHeader( remainingLength,
                                           pIndex,
                                           packetId );
        /* Serialize properties. */
        pIndex = encodeVariableLength( pIndex, propertyLength );

        if( propertyLength > 0U )
        {
            ( void ) memcpy( ( void * ) pIndex, ( const void * ) pSubscribeProperties->pBuffer, ( size_t ) propertyLength );
            pIndex = &pIndex[ ( size_t ) propertyLength ];
        }

        /* Serialize each subscription topic filter and QoS. */
        for( i = 0; i < subscriptionCount; i++ )
        {
            uint8_t subscriptionOptions = 0U;
            pIndex = encodeString( pIndex,
                                   pSubscriptionList[ i ].pTopicFilter,
                                   ( uint16_t ) pSubscriptionList[ i ].topicFilterLength );

            /* Place the subscription options. */
            if( pSubscriptionList[ i ].qos == MQTTQoS1 )
            {
                LogInfo( ( "Adding QoS as QoS 1 in SUBSCRIBE payload" ) );
                UINT8_SET_BIT( subscriptionOptions, MQTT_SUBSCRIBE_QOS1 );
            }
            else if( pSubscriptionList[ i ].qos == MQTTQoS2 )
            {
                LogInfo( ( "Adding QoS as QoS 2 in SUBSCRIBE payload" ) );
                UINT8_SET_BIT( subscriptionOptions, MQTT_SUBSCRIBE_QOS2 );
            }
            else
            {
                LogInfo( ( "Adding QoS as QoS 0 in SUBSCRIBE payload" ) );
            }

            if( pSubscriptionList[ i ].noLocalOption )
            {
                LogInfo( ( "Adding noLocalOption in SUBSCRIBE payload" ) );
                UINT8_SET_BIT( subscriptionOptions, MQTT_SUBSCRIBE_NO_LOCAL );
            }
            else
            {
                LogDebug( ( "Adding noLocalOption as 0 in SUBSCRIBE payload" ) );
            }

            if( pSubscriptionList[ i ].retainAsPublishedOption )
            {
                LogInfo( ( " retainAsPublishedOption in SUBSCRIBE payload" ) );
                UINT8_SET_BIT( subscriptionOptions, MQTT_SUBSCRIBE_RETAIN_AS_PUBLISHED );
            }
            else
            {
                LogDebug( ( "retainAsPublishedOption as 0 in SUBSCRIBE payload" ) );
            }

            if( pSubscriptionList[ i ].retainHandlingOption == retainSendOnSub )
            {
                LogInfo( ( "Send Retain messages at the time of subscribe" ) );
            }
            else if( pSubscriptionList[ i ].retainHandlingOption == retainSendOnSubIfNotPresent )
            {
                LogInfo( ( "Send retained messages at subscribe only if the subscription does not currently exist" ) );
                UINT8_SET_BIT( subscriptionOptions, MQTT_SUBSCRIBE_RETAIN_HANDLING1 );
            }
            else
            {
                LogInfo( ( "Do not send retained messages at subscribe" ) );
                UINT8_SET_BIT( subscriptionOptions, MQTT_SUBSCRIBE_RETAIN_HANDLING2 );
            }

            *pIndex = subscriptionOptions;
            pIndex = &pIndex[ 1 ];
        }

        LogDebug( ( "Length of serialized SUBSCRIBE packet is %lu.",
                    ( ( unsigned long ) ( pIndex - pFixedBuffer->pBuffer ) ) ) );
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_GetUnsubscribePacketSize( const MQTTSubscribeInfo_t * pSubscriptionList,
                                            size_t subscriptionCount,
                                            const MQTTPropBuilder_t * pUnsubscribeProperties,
                                            uint32_t * pRemainingLength,
                                            uint32_t * pPacketSize,
                                            uint32_t maxPacketSize )
{
    MQTTStatus_t status = MQTTSuccess;
    uint32_t propertyLength = 0U;

    /* Validate parameters. */
    if( ( pSubscriptionList == NULL ) || ( pRemainingLength == NULL ) ||
        ( pPacketSize == NULL ) )
    {
        LogError( ( "Argument cannot be NULL: pSubscriptionList=%p, "
                    "pRemainingLength=%p, pPacketSize=%p.",
                    ( const void * ) pSubscriptionList,
                    ( void * ) pRemainingLength,
                    ( void * ) pPacketSize ) );
        status = MQTTBadParameter;
    }
    else if( maxPacketSize == 0U )
    {
        LogError( ( "Max Packet size cannot be 0" ) );
        status = MQTTBadParameter;
    }
    else if( subscriptionCount == 0U )
    {
        LogError( ( "Subscription count is 0." ) );
        status = MQTTBadParameter;
    }
    else
    {
        if( ( pUnsubscribeProperties != NULL ) && ( pUnsubscribeProperties->pBuffer != NULL ) )
        {
            /* The value must fit in a 32-bit variable all the while being small enough to
             * be properly encoded in a variable integer format. */
            if( CHECK_SIZE_T_OVERFLOWS_32BIT( pUnsubscribeProperties->currentIndex ) ||
                ( pUnsubscribeProperties->currentIndex > MQTT_MAX_REMAINING_LENGTH ) )
            {
                LogError( ( "Un-Subscription properties must be less than 268435456 "
                            "to be able to fit in a MQTT packet." ) );
                status = MQTTBadParameter;
            }
            else
            {
                propertyLength = ( uint32_t ) pUnsubscribeProperties->currentIndex;
            }
        }

        if( status == MQTTSuccess )
        {
            /* Calculate the MQTT UNSUBSCRIBE packet size. */
            status = calculateSubscriptionPacketSize( pSubscriptionList,
                                                      subscriptionCount,
                                                      pRemainingLength,
                                                      pPacketSize,
                                                      propertyLength,
                                                      maxPacketSize,
                                                      MQTT_TYPE_UNSUBSCRIBE );
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_ValidateUnsubscribeProperties( const MQTTPropBuilder_t * pPropertyBuilder )
{
    MQTTStatus_t status = MQTTSuccess;
    uint32_t propertyLength = 0U;
    uint8_t * pIndex = NULL;


    if( ( pPropertyBuilder != NULL ) && ( pPropertyBuilder->pBuffer != NULL ) )
    {
        if( CHECK_SIZE_T_OVERFLOWS_32BIT( pPropertyBuilder->currentIndex ) ||
            ( pPropertyBuilder->currentIndex >= MQTT_REMAINING_LENGTH_INVALID ) )
        {
            LogError( ( "Property length cannot have more than %" PRIu32 " bytes", MQTT_REMAINING_LENGTH_INVALID ) );
            status = MQTTBadParameter;
        }
        else
        {
            propertyLength = ( uint32_t ) pPropertyBuilder->currentIndex;
            pIndex = pPropertyBuilder->pBuffer;
        }
    }

    while( ( propertyLength > 0U ) && ( status == MQTTSuccess ) )
    {
        uint8_t propertyId = *pIndex;
        pIndex = &pIndex[ 1 ];
        propertyLength -= 1U;

        switch( propertyId )
        {
            case MQTT_USER_PROPERTY_ID:
               {
                   const char * key, * value;
                   size_t keyLength, valueLength;
                   status = decodeUserProp( &key, &keyLength, &value, &valueLength, &propertyLength, &pIndex );

                   if( status == MQTTSuccess )
                   {
                       LogTrace( ( "Processing User Property %.*s:%.*s",
                                   ( int ) keyLength, key,
                                   ( int ) valueLength, value ) );
                   }
               }
               break;

            default:
                status = MQTTBadParameter;
                break;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_SerializeUnsubscribe( const MQTTSubscribeInfo_t * pSubscriptionList,
                                        size_t subscriptionCount,
                                        const MQTTPropBuilder_t * pUnsubscribeProperties,
                                        uint16_t packetId,
                                        uint32_t remainingLength,
                                        const MQTTFixedBuffer_t * pFixedBuffer )
{
    MQTTStatus_t status = MQTTSuccess;
    size_t i = 0;
    uint32_t propertyLength = 0U;
    uint8_t * pIndex = NULL;

    if( ( pUnsubscribeProperties != NULL ) && ( pUnsubscribeProperties->pBuffer != NULL ) )
    {
        if( CHECK_SIZE_T_OVERFLOWS_32BIT( pUnsubscribeProperties->currentIndex ) ||
            ( pUnsubscribeProperties->currentIndex >= MQTT_REMAINING_LENGTH_INVALID ) )
        {
            LogError( ( "Unsubscribe properties cannot have a length more than 268435455." ) );
            status = MQTTBadParameter;
        }
        else
        {
            propertyLength = ( uint32_t ) pUnsubscribeProperties->currentIndex;
        }
    }

    if( status == MQTTSuccess )
    {
        /* Validate all the parameters. */
        status = validateSubscriptionSerializeParams( pSubscriptionList,
                                                      subscriptionCount,
                                                      packetId,
                                                      remainingLength,
                                                      pFixedBuffer );
    }

    if( status == MQTTSuccess )
    {
        /* Get the start of the buffer to the iterator variable. */
        pIndex = pFixedBuffer->pBuffer;

        pIndex = serializeUnsubscribeHeader( remainingLength, pIndex, packetId );

        /* Serialize the properties. */
        pIndex = encodeVariableLength( pIndex, propertyLength );

        if( propertyLength > 0U )
        {
            ( void ) memcpy( ( void * ) pIndex, ( const void * ) pUnsubscribeProperties->pBuffer, ( size_t ) propertyLength );
            pIndex = &pIndex[ ( size_t ) propertyLength ];
        }

        /* Serialize each subscription topic filter. */
        for( i = 0; i < subscriptionCount; i++ )
        {
            pIndex = encodeString( pIndex,
                                   pSubscriptionList[ i ].pTopicFilter,
                                   ( uint16_t ) pSubscriptionList[ i ].topicFilterLength );
        }

        LogDebug( ( "Length of serialized UNSUBSCRIBE packet is %lu.",
                    ( ( unsigned long ) ( pIndex - pFixedBuffer->pBuffer ) ) ) );
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_GetPublishPacketSize( const MQTTPublishInfo_t * pPublishInfo,
                                        const MQTTPropBuilder_t * pPublishProperties,
                                        uint32_t * pRemainingLength,
                                        uint32_t * pPacketSize,
                                        uint32_t maxPacketSize )
{
    MQTTStatus_t status = MQTTSuccess;
    uint32_t propertyLength = 0U;

    if( ( pPublishProperties != NULL ) && ( pPublishProperties->pBuffer != NULL ) )
    {
        /* The value must fit in a 32-bit variable all the while being small enough to
         * be properly encoded in a variable integer format. */
        if( CHECK_SIZE_T_OVERFLOWS_32BIT( pPublishProperties->currentIndex ) ||
            ( pPublishProperties->currentIndex > MQTT_MAX_REMAINING_LENGTH ) )
        {
            LogError( ( "Publish properties must be less than 268435456 "
                        "to be able to fit in a MQTT packet." ) );
            status = MQTTBadParameter;
        }
        else
        {
            propertyLength = ( uint32_t ) pPublishProperties->currentIndex;
        }
    }

    if( ( pPublishInfo == NULL ) || ( pRemainingLength == NULL ) || ( pPacketSize == NULL ) )
    {
        LogError( ( "Argument cannot be NULL: pPublishInfo=%p, "
                    "pRemainingLength=%p, pPacketSize=%p.",
                    ( const void * ) pPublishInfo,
                    ( void * ) pRemainingLength,
                    ( void * ) pPacketSize ) );
        status = MQTTBadParameter;
    }
    else if( CHECK_SIZE_T_OVERFLOWS_16BIT( pPublishInfo->topicNameLength ) )
    {
        LogError( ( "Topic name length must be smaller than 65535." ) );
        status = MQTTBadParameter;
    }
    else if( CHECK_SIZE_T_OVERFLOWS_32BIT( pPublishInfo->payloadLength ) ||
             ( pPublishInfo->payloadLength >= MQTT_REMAINING_LENGTH_INVALID ) )
    {
        LogError( ( "Payload must be smaller than 268435455." ) );
        status = MQTTBadParameter;
    }
    else
    {
        status = calculatePublishPacketSize( pPublishInfo,
                                             pRemainingLength,
                                             pPacketSize,
                                             maxPacketSize,
                                             propertyLength );
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_SerializePublish( const MQTTPublishInfo_t * pPublishInfo,
                                    const MQTTPropBuilder_t * pPublishProperties,
                                    uint16_t packetId,
                                    uint32_t remainingLength,
                                    const MQTTFixedBuffer_t * pFixedBuffer )
{
    MQTTStatus_t status = MQTTSuccess;
    uint32_t packetSize = 0;

    if( ( pFixedBuffer == NULL ) || ( pPublishInfo == NULL ) )
    {
        LogError( ( "Argument cannot be NULL: pFixedBuffer=%p, "
                    "pPublishInfo=%p.",
                    ( const void * ) pFixedBuffer,
                    ( const void * ) pPublishInfo ) );
        status = MQTTBadParameter;
    }
    /* A buffer must be configured for serialization. */
    else if( pFixedBuffer->pBuffer == NULL )
    {
        LogError( ( "Argument cannot be NULL: pFixedBuffer->pBuffer is NULL." ) );
        status = MQTTBadParameter;
    }

    /* For serializing a publish, if there exists a payload, then the buffer
     * cannot be NULL. */
    else if( ( pPublishInfo->payloadLength > 0U ) && ( pPublishInfo->pPayload == NULL ) )
    {
        LogError( ( "A nonzero payload length requires a non-NULL payload: "
                    "payloadLength=%lu, pPayload=%p.",
                    ( unsigned long ) pPublishInfo->payloadLength,
                    pPublishInfo->pPayload ) );
        status = MQTTBadParameter;
    }
    else if( ( pPublishInfo->pTopicName == NULL ) || ( pPublishInfo->topicNameLength == 0U ) )
    {
        LogError( ( "Invalid topic name for PUBLISH: pTopicName=%p, "
                    "topicNameLength=%hu.",
                    ( const void * ) pPublishInfo->pTopicName,
                    ( unsigned short ) pPublishInfo->topicNameLength ) );
        status = MQTTBadParameter;
    }
    else if( ( pPublishInfo->qos != MQTTQoS0 ) && ( packetId == 0U ) )
    {
        LogError( ( "Packet ID is 0 for PUBLISH with QoS=%u.",
                    ( unsigned int ) pPublishInfo->qos ) );
        status = MQTTBadParameter;
    }
    else if( ( pPublishInfo->dup == true ) && ( pPublishInfo->qos == MQTTQoS0 ) )
    {
        LogError( ( "Duplicate flag is set for PUBLISH with Qos 0." ) );
        status = MQTTBadParameter;
    }
    else if( CHECK_SIZE_T_OVERFLOWS_16BIT( pPublishInfo->topicNameLength ) )
    {
        LogError( ( "topicNameLength must be less than 65535 to fit in 16-bits." ) );
        status = MQTTBadParameter;
    }
    else if( remainingLength >= MQTT_REMAINING_LENGTH_INVALID )
    {
        LogError( ( "Remaining length cannot be greater than 268435455." ) );
        status = MQTTBadParameter;
    }
    else if( ( pPublishProperties != NULL ) &&
             ( pPublishProperties->pBuffer != NULL ) &&
             ( CHECK_SIZE_T_OVERFLOWS_32BIT( pPublishProperties->currentIndex ) ||
               ( pPublishProperties->currentIndex > MQTT_MAX_REMAINING_LENGTH ) ) )
    {
        LogError( ( "Property length cannot be greater than 268435455." ) );
        status = MQTTBadParameter;
    }
    else
    {
        /* Length of serialized packet = First byte
         *                                + Length of encoded remaining length
         *                                + Remaining length. */
        packetSize = 1U + variableLengthEncodedSize( remainingLength )
                     + remainingLength;
    }

    if( ( status == MQTTSuccess ) && ( packetSize > pFixedBuffer->size ) )
    {
        LogError( ( "Buffer size of %" PRIu32 " is not sufficient to hold "
                                              "serialized PUBLISH packet of size of %" PRIu32 ".",
                    ( uint32_t ) pFixedBuffer->size,
                    packetSize ) );
        status = MQTTNoMemory;
    }

    if( status == MQTTSuccess )
    {
        /* Serialize publish with header and payload. */
        serializePublishCommon( pPublishInfo,
                                pPublishProperties,
                                remainingLength,
                                packetId,
                                pFixedBuffer,
                                true );
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_SerializePublishHeader( const MQTTPublishInfo_t * pPublishInfo,
                                          const MQTTPropBuilder_t * pPublishProperties,
                                          uint16_t packetId,
                                          uint32_t remainingLength,
                                          const MQTTFixedBuffer_t * pFixedBuffer,
                                          size_t * pHeaderSize )
{
    MQTTStatus_t status = MQTTSuccess;
    size_t packetSize = 0;

    if( ( pFixedBuffer == NULL ) || ( pPublishInfo == NULL ) ||
        ( pHeaderSize == NULL ) )
    {
        LogError( ( "Argument cannot be NULL: pFixedBuffer=%p, "
                    "pPublishInfo=%p, pHeaderSize=%p.",
                    ( const void * ) pFixedBuffer,
                    ( const void * ) pPublishInfo,
                    ( void * ) pHeaderSize ) );
        status = MQTTBadParameter;
    }
    /* A buffer must be configured for serialization. */
    else if( pFixedBuffer->pBuffer == NULL )
    {
        LogError( ( "Argument cannot be NULL: pFixedBuffer->pBuffer is NULL." ) );
        status = MQTTBadParameter;
    }
    else if( ( pPublishInfo->pTopicName == NULL ) || ( pPublishInfo->topicNameLength == 0U ) )
    {
        LogError( ( "Invalid topic name for publish: pTopicName=%p, "
                    "topicNameLength=%hu.",
                    ( const void * ) pPublishInfo->pTopicName,
                    ( unsigned short ) pPublishInfo->topicNameLength ) );
        status = MQTTBadParameter;
    }
    else if( CHECK_SIZE_T_OVERFLOWS_16BIT( pPublishInfo->topicNameLength ) )
    {
        LogError( ( "topicNameLength must be less than 65535 to fit in 16-bits." ) );
        status = MQTTBadParameter;
    }
    else if( ( pPublishInfo->qos != MQTTQoS0 ) && ( packetId == 0U ) )
    {
        LogError( ( "Packet Id is 0 for publish with QoS=%hu.",
                    ( unsigned short ) pPublishInfo->qos ) );
        status = MQTTBadParameter;
    }
    else if( ( pPublishInfo->dup == true ) && ( pPublishInfo->qos == MQTTQoS0 ) )
    {
        LogError( ( "Duplicate flag is set for PUBLISH with Qos 0." ) );
        status = MQTTBadParameter;
    }
    else if( remainingLength >= MQTT_REMAINING_LENGTH_INVALID )
    {
        LogError( ( "Remaining length cannot be greater than 268435455." ) );
        status = MQTTBadParameter;
    }
    else if( remainingLength < pPublishInfo->payloadLength )
    {
        LogError( ( "Remaining length cannot be less than the payload length." ) );
        status = MQTTBadParameter;
    }
    else
    {
        /* Length of serialized packet = First byte
         *                               + Length of encoded remaining length
         *                               + Remaining length
         *                               - Payload Length.
         */
        uint32_t packetSizeU32 = 1U + variableLengthEncodedSize( remainingLength )
                                 + remainingLength
                                 - ( ( uint32_t ) pPublishInfo->payloadLength );

        if( CHECK_U32T_OVERFLOWS_SIZE_T( packetSizeU32 ) )
        {
            LogError( ( "Length of serialized packet will not fit in size_t variable." ) );

            /* More details at: https://github.com/FreeRTOS/coreMQTT/blob/main/MISRA.md#rule-143 */
            /* coverity[misra_c_2012_rule_14_3_violation] */
            status = MQTTBadParameter;
        }
        else
        {
            packetSize = ( size_t ) packetSizeU32;
        }
    }

    if( ( status == MQTTSuccess ) && ( packetSize > pFixedBuffer->size ) )
    {
        LogError( ( "Buffer size of %lu is not sufficient to hold "
                    "serialized PUBLISH header packet of size of %lu.",
                    ( unsigned long ) pFixedBuffer->size,
                    ( unsigned long ) ( packetSize - pPublishInfo->payloadLength ) ) );
        status = MQTTNoMemory;
    }

    if( status == MQTTSuccess )
    {
        /* Serialize publish without copying the payload. */
        serializePublishCommon( pPublishInfo,
                                pPublishProperties,
                                remainingLength,
                                packetId,
                                pFixedBuffer,
                                false );

        /* Header size is the same as calculated packet size. */
        *pHeaderSize = packetSize;
    }

    return status;
}

/*-----------------------------------------------------------*/

/*-----------------------------------------------------------*/

/**
 * @brief Serialize a publish ACK packet with properties into pFixedBuffer.
 * Called only when pReasonCode != NULL and pAckProperties != NULL.
 */
static MQTTStatus_t serializeAckWithProperties( const MQTTFixedBuffer_t * pFixedBuffer,
                                                uint8_t packetType,
                                                uint16_t packetId,
                                                const MQTTPropBuilder_t * pAckProperties,
                                                const MQTTSuccessFailReasonCode_t * pReasonCode )
{
    MQTTStatus_t status = MQTTSuccess;
    uint32_t ackPacketRemainingLength;
    uint32_t ackPacketSize;
    uint8_t * pIndex;

    ackPacketRemainingLength = 3U +
                               variableLengthEncodedSize( ( uint32_t ) pAckProperties->currentIndex ) +
                               ( ( uint32_t ) pAckProperties->currentIndex );

    if( ackPacketRemainingLength > MQTT_MAX_REMAINING_LENGTH )
    {
        LogError( ( "Packet remaining length must be smaller than 268435456." ) );
        status = MQTTBadParameter;
    }
    else
    {
        ackPacketSize = 1U +
                        variableLengthEncodedSize( ackPacketRemainingLength ) +
                        ackPacketRemainingLength;

        if( pFixedBuffer->size < ackPacketSize )
        {
            LogError( ( "Not enough space in the buffer to encode properties." ) );
            status = MQTTBadParameter;
        }
        else
        {
            pFixedBuffer->pBuffer[ 0 ] = packetType;
            pIndex = encodeVariableLength( &pFixedBuffer->pBuffer[ 1 ], ackPacketRemainingLength );
            pIndex[ 0 ] = UINT16_HIGH_BYTE( packetId );
            pIndex[ 1 ] = UINT16_LOW_BYTE( packetId );
            pIndex[ 2 ] = ( uint8_t ) ( *pReasonCode );
            pIndex = encodeVariableLength( &pIndex[ 3 ], ( uint32_t ) pAckProperties->currentIndex );
            ( void ) memcpy( pIndex, pAckProperties->pBuffer, pAckProperties->currentIndex );
        }
    }

    return status;
}

/**
 * @brief Validate parameters and serialize a publish ACK packet body.
 * Handles the three cases: no reason code, reason code only, reason code + properties.
 */
static MQTTStatus_t serializeAckBody( const MQTTFixedBuffer_t * pFixedBuffer,
                                      uint8_t packetType,
                                      uint16_t packetId,
                                      const MQTTPropBuilder_t * pAckProperties,
                                      const MQTTSuccessFailReasonCode_t * pReasonCode )
{
    MQTTStatus_t status = MQTTSuccess;

    pFixedBuffer->pBuffer[ 0 ] = packetType;

    if( pReasonCode == NULL )
    {
        /* Simple 4-byte ACK: type + remaining(2) + packetId(2). */
        pFixedBuffer->pBuffer[ 1 ] = MQTT_PACKET_SIMPLE_ACK_REMAINING_LENGTH;
        pFixedBuffer->pBuffer[ 2 ] = UINT16_HIGH_BYTE( packetId );
        pFixedBuffer->pBuffer[ 3 ] = UINT16_LOW_BYTE( packetId );
    }
    else if( pFixedBuffer->size < ( MQTT_PUBLISH_ACK_PACKET_SIZE + 2U ) )
    {
        LogError( ( "Not enough space for reason code." ) );
        status = MQTTBadParameter;
    }
    else if( ( pAckProperties == NULL ) || ( pAckProperties->pBuffer == NULL ) )
    {
        /* Reason code present, no properties — must still encode property length 0x00. */
        pFixedBuffer->pBuffer[ 1 ] = MQTT_PACKET_SIMPLE_ACK_REMAINING_LENGTH + 2U;
        pFixedBuffer->pBuffer[ 2 ] = UINT16_HIGH_BYTE( packetId );
        pFixedBuffer->pBuffer[ 3 ] = UINT16_LOW_BYTE( packetId );
        pFixedBuffer->pBuffer[ 4 ] = ( uint8_t ) ( *pReasonCode );
        pFixedBuffer->pBuffer[ 5 ] = 0x00; /* property length = 0 */
    }
    else
    {
        status = serializeAckWithProperties( pFixedBuffer, packetType, packetId,
                                             pAckProperties, pReasonCode );
    }

    return status;
}

MQTTStatus_t MQTT_SerializeAck( const MQTTFixedBuffer_t * pFixedBuffer,
                                uint8_t packetType,
                                uint16_t packetId,
                                const MQTTPropBuilder_t * pAckProperties,
                                const MQTTSuccessFailReasonCode_t * pReasonCode )
{
    MQTTStatus_t status = MQTTSuccess;

    if( pFixedBuffer == NULL )
    {
        LogError( ( "Provided buffer is NULL." ) );
        status = MQTTBadParameter;
    }
    else if( pFixedBuffer->pBuffer == NULL )
    {
        LogError( ( "pFixedBuffer->pBuffer cannot be NULL." ) );
        status = MQTTBadParameter;
    }
    else if( pFixedBuffer->size < MQTT_PUBLISH_ACK_PACKET_SIZE )
    {
        LogError( ( "Insufficient memory for packet." ) );
        status = MQTTNoMemory;
    }
    else if( packetId == 0U )
    {
        LogError( ( "Packet ID cannot be 0." ) );
        status = MQTTBadParameter;
    }
    else if( ( pReasonCode == NULL ) && ( pAckProperties != NULL ) )
    {
        LogError( ( "A reason code must be provided if there are properties." ) );
        status = MQTTBadParameter;
    }
    else if( ( pReasonCode != NULL ) && ( validateReasonCodeForAck( packetType, *pReasonCode ) != MQTTSuccess ) )
    {
        LogError( ( "Invalid reason code for the ACK type." ) );
        status = MQTTBadParameter;
    }
    else if( ( pAckProperties != NULL ) &&
             ( CHECK_SIZE_T_OVERFLOWS_32BIT( pAckProperties->currentIndex ) ||
               ( pAckProperties->currentIndex >= MQTT_REMAINING_LENGTH_INVALID ) ) )
    {
        LogError( ( "ACK properties must be smaller than 268435456." ) );
        status = MQTTBadParameter;
    }
    else
    {
        switch( packetType )
        {
            case MQTT_PACKET_TYPE_PUBACK:
            case MQTT_PACKET_TYPE_PUBREC:
            case MQTT_PACKET_TYPE_PUBREL:
            case MQTT_PACKET_TYPE_PUBCOMP:
                status = serializeAckBody( pFixedBuffer, packetType, packetId,
                                           pAckProperties, pReasonCode );
                break;

            default:
                LogError( ( "Packet type is not a publish ACK: Packet type=%02x",
                            ( unsigned int ) packetType ) );
                status = MQTTBadParameter;
                break;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_GetDisconnectPacketSize( const MQTTPropBuilder_t * pDisconnectProperties,
                                           uint32_t * pRemainingLength,
                                           uint32_t * pPacketSize,
                                           uint32_t maxPacketSize,
                                           const MQTTSuccessFailReasonCode_t * pReasonCode )
{
    MQTTStatus_t status = MQTTSuccess;
    uint32_t length = 0U;
    uint32_t packetSize = 0U;
    uint32_t propertyLength = 0U;

    /* Validate the arguments. */
    if( ( pReasonCode == NULL ) && ( pDisconnectProperties != NULL ) )
    {
        LogError( ( "Reason code must be specified if the properties are non-NULL." ) );
        status = MQTTBadParameter;
    }
    else if( ( pRemainingLength == NULL ) || ( pPacketSize == NULL ) )
    {
        LogError( ( "Argument cannot be NULL:"
                    "pRemainingLength=%p, pPacketSize=%p.",
                    ( void * ) pRemainingLength,
                    ( void * ) pPacketSize ) );
        status = MQTTBadParameter;
    }
    else if( maxPacketSize == 0U )
    {
        LogError( ( "Max packet size cannot be zero." ) );
        status = MQTTBadParameter;
    }
    else if( ( pReasonCode != NULL ) && ( validateDisconnectResponse( *pReasonCode, false ) != MQTTSuccess ) )
    {
        LogError( ( "Invalid reason code." ) );
        status = MQTTBadParameter;
    }
    else if( pReasonCode != NULL )
    {
        /* Reason code. */
        length += 1U;
    }
    else
    {
        /* No reason code provided. No need to update the length. */
    }

    if( status == MQTTSuccess )
    {
        if( ( pDisconnectProperties != NULL ) && ( pDisconnectProperties->pBuffer != NULL ) )
        {
            /* The value must fit in a 32-bit variable all the while being small enough to
             * be properly encoded in a variable integer format. */
            if( CHECK_SIZE_T_OVERFLOWS_32BIT( pDisconnectProperties->currentIndex ) ||
                ( pDisconnectProperties->currentIndex > MQTT_MAX_REMAINING_LENGTH ) )
            {
                LogError( ( "Disconnect properties must be less than 268435456 "
                            "to be able to fit in a MQTT packet." ) );
                status = MQTTBadParameter;
            }
            else
            {
                propertyLength = ( uint32_t ) pDisconnectProperties->currentIndex;
            }
        }

        if( status == MQTTSuccess )
        {
            /* Validate the length. The sum of:
             * Bytes required to encode the properties +
             * Actual properties +
             * Optional reason code (which is depicted by length)
             *
             * Must be less than the maximum allowed remaining length.
             */
            if( ( propertyLength + variableLengthEncodedSize( propertyLength ) + length ) < MQTT_MAX_REMAINING_LENGTH )
            {
                length += variableLengthEncodedSize( propertyLength ) + propertyLength;
                *pRemainingLength = length;
            }
            else
            {
                LogError( ( "The properties + reason code cannot fit in MQTT_MAX_REMAINING_LENGTH bytes." ) );
                status = MQTTBadParameter;
            }
        }
    }

    if( status == MQTTSuccess )
    {
        /* Packet size should be less than max allowed by the server. It is calculated as:
         * MQTT Disconnect header byte +
         * Bytes required to encode the remaining length +
         * The remaining length (which includes properties and error code).
         */
        packetSize = 1U + variableLengthEncodedSize( length ) + length;

        if( packetSize > maxPacketSize )
        {
            LogError( ( "Packet Size greater than Max Packet Size specified in the CONNACK" ) );
            status = MQTTBadParameter;
        }
        else
        {
            *pPacketSize = packetSize;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_SerializeDisconnect( const MQTTPropBuilder_t * pDisconnectProperties,
                                       const MQTTSuccessFailReasonCode_t * pReasonCode,
                                       uint32_t remainingLength,
                                       const MQTTFixedBuffer_t * pFixedBuffer )
{
    MQTTStatus_t status = MQTTSuccess;
    uint8_t * pIndex = NULL;
    uint32_t packetSize = 0U;
    uint32_t propertyLength = 0U;

    if( ( pDisconnectProperties != NULL ) && ( pDisconnectProperties->pBuffer != NULL ) )
    {
        if( CHECK_SIZE_T_OVERFLOWS_32BIT( pDisconnectProperties->currentIndex ) ||
            ( pDisconnectProperties->currentIndex >= MQTT_REMAINING_LENGTH_INVALID ) )
        {
            LogError( ( "Disconnect properties cannot have a length more than 268435455." ) );
            status = MQTTBadParameter;
        }
        else
        {
            propertyLength = ( uint32_t ) pDisconnectProperties->currentIndex;
        }
    }

    /* Validate arguments. */
    if( pFixedBuffer == NULL )
    {
        LogError( ( "pFixedBuffer cannot be NULL." ) );
        status = MQTTBadParameter;
    }
    else if( pFixedBuffer->pBuffer == NULL )
    {
        LogError( ( "pFixedBuffer->pBuffer cannot be NULL." ) );
        status = MQTTBadParameter;
    }
    else if( ( pReasonCode == NULL ) && ( pDisconnectProperties != NULL ) )
    {
        LogError( ( "Reason code must be provided if the properties are non-NULL." ) );
        status = MQTTBadParameter;
    }
    else if( remainingLength >= MQTT_REMAINING_LENGTH_INVALID )
    {
        LogError( ( "Remaining length cannot be greater than 268435455." ) );
        status = MQTTBadParameter;
    }
    else
    {
        /* Length of serialized packet = First byte
         *                                + Length of encoded remaining length
         *                                + Remaining length. */
        packetSize = 1U + variableLengthEncodedSize( remainingLength ) + remainingLength;
    }

    if( status == MQTTSuccess )
    {
        if( pFixedBuffer->size < packetSize )
        {
            LogError( ( "Buffer size of %lu is not sufficient to hold "
                        "serialized DISCONNECT packet of size of %lu.",
                        ( unsigned long ) pFixedBuffer->size,
                        ( unsigned long ) packetSize ) );
            status = MQTTNoMemory;
        }
    }

    if( status == MQTTSuccess )
    {
        pIndex = pFixedBuffer->pBuffer;
        pIndex = serializeDisconnectFixed( pIndex,
                                           pReasonCode,
                                           remainingLength );

        pIndex = encodeVariableLength( pIndex, propertyLength );

        if( propertyLength > 0U )
        {
            ( void ) memcpy( ( void * ) pIndex, ( const void * ) pDisconnectProperties->pBuffer, ( size_t ) propertyLength );
            pIndex = &pIndex[ ( size_t ) propertyLength ];
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_GetPingreqPacketSize( uint32_t * pPacketSize )
{
    MQTTStatus_t status = MQTTSuccess;

    if( pPacketSize == NULL )
    {
        LogError( ( "pPacketSize is NULL." ) );
        status = MQTTBadParameter;
    }
    else
    {
        /* MQTT PINGREQ packets always have the same size. */
        *pPacketSize = MQTT_PACKET_PINGREQ_SIZE;
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_SerializePingreq( const MQTTFixedBuffer_t * pFixedBuffer )
{
    MQTTStatus_t status = MQTTSuccess;

    if( pFixedBuffer == NULL )
    {
        LogError( ( "pFixedBuffer is NULL." ) );
        status = MQTTBadParameter;
    }
    else if( pFixedBuffer->pBuffer == NULL )
    {
        LogError( ( "pFixedBuffer->pBuffer cannot be NULL." ) );
        status = MQTTBadParameter;
    }
    else
    {
        /* All parameters are good. */
    }

    if( status == MQTTSuccess )
    {
        if( pFixedBuffer->size < MQTT_PACKET_PINGREQ_SIZE )
        {
            LogError( ( "Buffer size of %lu is not sufficient to hold "
                        "serialized PINGREQ packet of size of %" PRIu32 ".",
                        ( unsigned long ) pFixedBuffer->size,
                        ( uint32_t ) MQTT_PACKET_PINGREQ_SIZE ) );
            status = MQTTNoMemory;
        }
    }

    if( status == MQTTSuccess )
    {
        /* Ping request packets are always the same. */
        pFixedBuffer->pBuffer[ 0 ] = MQTT_PACKET_TYPE_PINGREQ;
        pFixedBuffer->pBuffer[ 1 ] = 0x00;
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_DeserializePublish( const MQTTPacketInfo_t * pIncomingPacket,
                                      uint16_t * pPacketId,
                                      MQTTPublishInfo_t * pPublishInfo,
                                      MQTTPropBuilder_t * propBuffer,
                                      uint32_t maxPacketSize,
                                      uint16_t topicAliasMax )
{
    MQTTStatus_t status = MQTTSuccess;

    if( ( pIncomingPacket == NULL ) || ( pPacketId == NULL ) || ( pPublishInfo == NULL ) )
    {
        LogError( ( "Argument cannot be NULL: pIncomingPacket=%p, "
                    "pPacketId=%p, pPublishInfo=%p",
                    ( const void * ) pIncomingPacket,
                    ( void * ) pPacketId,
                    ( void * ) pPublishInfo ) );
        status = MQTTBadParameter;
    }
    else if( ( pIncomingPacket->type & 0xF0U ) != MQTT_PACKET_TYPE_PUBLISH )
    {
        LogError( ( "Packet is not publish. Packet type: %02x.",
                    ( unsigned int ) pIncomingPacket->type ) );
        status = MQTTBadParameter;
    }
    else if( pIncomingPacket->pRemainingData == NULL )
    {
        LogError( ( "Argument cannot be NULL: "
                    "pIncomingPacket->pRemainingData is NULL." ) );
        status = MQTTBadParameter;
    }
    else if( pIncomingPacket->remainingLength >= MQTT_REMAINING_LENGTH_INVALID )
    {
        LogError( ( "Remaining length cannot be larger than MQTT maximum (268435456)." ) );
        status = MQTTBadParameter;
    }
    else if( ( pIncomingPacket->remainingLength +
               variableLengthEncodedSize( pIncomingPacket->remainingLength ) +
               1U ) > maxPacketSize )
    {
        LogError( ( "The incoming packet length is greater than the maximum packet size." ) );
        status = MQTTBadResponse;
    }
    else
    {
        status = deserializePublish( pIncomingPacket, pPacketId, pPublishInfo, propBuffer, topicAliasMax );
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_DeserializeConnAck( const MQTTPacketInfo_t * pIncomingPacket,
                                      bool * pSessionPresent,
                                      MQTTPropBuilder_t * pPropBuffer,
                                      MQTTConnectionProperties_t * pConnectProperties )
{
    MQTTStatus_t status = MQTTSuccess;

    if( pIncomingPacket == NULL )
    {
        LogError( ( "pIncomingPacket cannot be NULL." ) );
        status = MQTTBadParameter;
    }
    else if( pConnectProperties == NULL )
    {
        LogError( ( "pConnectProperties cannot be NULL." ) );
        status = MQTTBadParameter;
    }
    else if( pIncomingPacket->type != MQTT_PACKET_TYPE_CONNACK )
    {
        LogError( ( "MQTT_DeserializeConnAck should only be used to deserialize CONNACK packet." ) );
        status = MQTTBadParameter;
    }
    /* Pointer for session present cannot be NULL for CONNACK. */
    else if( pSessionPresent == NULL )
    {
        LogError( ( "pSessionPresent cannot be NULL for CONNACK packet." ) );
        status = MQTTBadParameter;
    }

    /* Pointer for remaining data cannot be NULL for packets other
     * than PINGRESP. */
    else if( pIncomingPacket->pRemainingData == NULL )
    {
        LogError( ( "Remaining data of incoming CONNACK packet is NULL." ) );
        status = MQTTBadParameter;
    }
    /* Max packet size cannot be 0. */
    else if( pConnectProperties->maxPacketSize == 0U )
    {
        LogError( ( "Max packet size cannot be 0." ) );
        status = MQTTBadParameter;
    }
    else if( CHECK_U32T_OVERFLOWS_SIZE_T( pIncomingPacket->remainingLength ) )
    {
        LogError( ( "pIncomingPacket->remainingLength cannot be represented by size_t." ) );

        /* More details at: https://github.com/FreeRTOS/coreMQTT/blob/main/MISRA.md#rule-143 */
        /* coverity[misra_c_2012_rule_14_3_violation] */
        status = MQTTBadParameter;
    }
    else if( ( pIncomingPacket->remainingLength +
               variableLengthEncodedSize( pIncomingPacket->remainingLength ) +
               1U ) > pConnectProperties->maxPacketSize )
    {
        LogError( ( "Incoming CONNACK packet Size cannot be greater than max packet size. " ) );
        status = MQTTBadResponse;
    }
    else
    {
        status = deserializeConnack( pConnectProperties,
                                     pIncomingPacket,
                                     pSessionPresent,
                                     pPropBuffer );
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_DeserializeAck( const MQTTPacketInfo_t * pIncomingPacket,
                                  uint16_t * pPacketId,
                                  MQTTReasonCodeInfo_t * pReasonCode,
                                  MQTTPropBuilder_t * pPropBuffer,
                                  const MQTTConnectionProperties_t * pConnectProperties )
{
    MQTTStatus_t status = MQTTSuccess;

    if( pIncomingPacket == NULL )
    {
        LogError( ( "pIncomingPacket cannot be NULL." ) );
        status = MQTTBadParameter;
    }
    else if( pConnectProperties == NULL )
    {
        LogError( ( "pConnectProperties cannot be NULL." ) );
        status = MQTTBadParameter;
    }
    else if( pIncomingPacket->type == MQTT_PACKET_TYPE_CONNACK )
    {
        LogError( ( "Please use MQTT_DeserializeConnAck for CONNACK packet." ) );
        status = MQTTBadParameter;
    }

    /* Pointer for packet identifier cannot be NULL for packets other than
     * CONNACK and PINGRESP. This function must not be called for CONNACK
     * handling and thus only PINGRESP is checked below. */
    else if( ( pPacketId == NULL ) &&
             ( pIncomingPacket->type != MQTT_PACKET_TYPE_PINGRESP ) )
    {
        LogError( ( "pPacketId cannot be NULL for packet type %02x.",
                    ( unsigned int ) pIncomingPacket->type ) );
        status = MQTTBadParameter;
    }

    /* Pointer for remaining data cannot be NULL for packets other
     * than PINGRESP. */
    else if( ( pIncomingPacket->pRemainingData == NULL ) &&
             ( pIncomingPacket->type != MQTT_PACKET_TYPE_PINGRESP ) )
    {
        LogError( ( "Remaining data of incoming packet is NULL." ) );
        status = MQTTBadParameter;
    }
    /* Max packet size cannot be 0. */
    else if( pConnectProperties->maxPacketSize == 0U )
    {
        LogError( ( "Max packet size cannot be 0." ) );
        status = MQTTBadParameter;
    }
    else if( CHECK_U32T_OVERFLOWS_SIZE_T( pIncomingPacket->remainingLength ) )
    {
        LogError( ( "Incoming packet length cannot be represented in a size_t variable." ) );

        /* More details at: https://github.com/FreeRTOS/coreMQTT/blob/main/MISRA.md#rule-143 */
        /* coverity[misra_c_2012_rule_14_3_violation] */
        status = MQTTBadParameter;
    }
    else if( ( pIncomingPacket->remainingLength +
               variableLengthEncodedSize( pIncomingPacket->remainingLength ) +
               1U ) > pConnectProperties->maxPacketSize )
    {
        LogError( ( "Packet Size cannot be greater than max packet size." ) );
        status = MQTTBadResponse;
    }
    else
    {
        /* Make sure response packet is a valid ack. */
        switch( pIncomingPacket->type )
        {
            case MQTT_PACKET_TYPE_PUBACK:
            case MQTT_PACKET_TYPE_PUBREC:
            case MQTT_PACKET_TYPE_PUBREL:
            case MQTT_PACKET_TYPE_PUBCOMP:
                status = deserializePubAcks( pIncomingPacket,
                                             pPacketId,
                                             pReasonCode,
                                             pConnectProperties->requestProblemInfo,
                                             pPropBuffer );

                if( ( status == MQTTSuccess ) && ( pIncomingPacket->remainingLength > 2U ) )
                {
                    /* More details at: https://github.com/FreeRTOS/coreMQTT/blob/main/MISRA.md#rule-105 */
                    /* coverity[misra_c_2012_rule_10_5_violation] */
                    status = logAckResponse( ( MQTTSuccessFailReasonCode_t ) ( *pReasonCode->reasonCode ),
                                             *pPacketId );
                }

                break;

            case MQTT_PACKET_TYPE_SUBACK:
            case MQTT_PACKET_TYPE_UNSUBACK:
                status = deserializeSubUnsubAck( pIncomingPacket, pPacketId, pReasonCode, pPropBuffer );
                break;

            case MQTT_PACKET_TYPE_PINGRESP:
                status = deserializePingresp( pIncomingPacket );
                break;

            /* Any other packet type is invalid. */
            default:
                LogError( ( "Function called with unknown packet type:(%02x).",
                            ( unsigned int ) pIncomingPacket->type ) );
                status = MQTTBadResponse;
                break;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_GetIncomingPacketTypeAndLength( TransportRecv_t readFunc,
                                                  NetworkContext_t * pNetworkContext,
                                                  MQTTPacketInfo_t * pIncomingPacket )
{
    MQTTStatus_t status = MQTTSuccess;
    int32_t bytesReceived = 0;

    if( pIncomingPacket == NULL )
    {
        LogError( ( "Invalid parameter: pIncomingPacket is NULL." ) );
        status = MQTTBadParameter;
    }
    else
    {
        /* Read a single byte. */
        bytesReceived = readFunc( pNetworkContext,
                                  &( pIncomingPacket->type ),
                                  1U );
    }

    if( bytesReceived == 1 )
    {
        /* Check validity. */
        if( incomingPacketValid( pIncomingPacket->type ) == true )
        {
            pIncomingPacket->remainingLength = getRemainingLength( readFunc,
                                                                   pNetworkContext );

            if( pIncomingPacket->remainingLength == MQTT_REMAINING_LENGTH_INVALID )
            {
                LogError( ( "Incoming packet remaining length invalid." ) );
                status = MQTTBadResponse;
            }
        }
        else
        {
            LogError( ( "Incoming packet invalid: Packet type=%u.",
                        ( unsigned int ) pIncomingPacket->type ) );
            status = MQTTBadResponse;
        }
    }
    else if( ( status != MQTTBadParameter ) && ( bytesReceived == 0 ) )
    {
        status = MQTTNoDataAvailable;
    }

    /* If the input packet was valid, then any other number of bytes received is
     * a failure. */
    else if( status != MQTTBadParameter )
    {
        LogError( ( "A single byte was not read from the transport: "
                    "transportStatus=%ld.",
                    ( long int ) bytesReceived ) );
        status = MQTTRecvFailed;
    }
    else
    {
        /* Input was invalid. */
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_UpdateDuplicatePublishFlag( uint8_t * pHeader,
                                              bool set )
{
    MQTTStatus_t status = MQTTSuccess;

    if( pHeader == NULL )
    {
        LogError( ( "Header cannot be NULL" ) );
        status = MQTTBadParameter;
    }
    else if( ( ( *pHeader ) & 0xF0U ) != MQTT_PACKET_TYPE_PUBLISH )
    {
        LogError( ( "Header is not publish packet header" ) );
        status = MQTTBadParameter;
    }
    else if( set == true )
    {
        UINT8_SET_BIT( *pHeader, MQTT_PUBLISH_FLAG_DUP );
    }
    else
    {
        UINT8_CLEAR_BIT( *pHeader, MQTT_PUBLISH_FLAG_DUP );
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_ProcessIncomingPacketTypeAndLength( const uint8_t * pBuffer,
                                                      const size_t * pIndex,
                                                      MQTTPacketInfo_t * pIncomingPacket )
{
    MQTTStatus_t status = MQTTSuccess;

    if( pIncomingPacket == NULL )
    {
        LogError( ( "Invalid parameter: pIncomingPacket is NULL." ) );
        status = MQTTBadParameter;
    }
    else if( pIndex == NULL )
    {
        LogError( ( "Invalid parameter: pIndex is NULL." ) );
        status = MQTTBadParameter;
    }
    else if( pBuffer == NULL )
    {
        LogError( ( "Invalid parameter: pBuffer is NULL." ) );
        status = MQTTBadParameter;
    }
    /* There should be at least one byte in the buffer */
    else if( *pIndex < 1U )
    {
        /* No data is available. There are 0 bytes received from the network
         * receive function. */
        status = MQTTNoDataAvailable;
    }
    else
    {
        /* At least one byte is present which should be deciphered. */
        pIncomingPacket->type = pBuffer[ 0 ];
    }

    if( status == MQTTSuccess )
    {
        /* Check validity. */
        if( incomingPacketValid( pIncomingPacket->type ) == true )
        {
            LogTrace( ( "Incoming packet type: %s",
                        MQTT_GetPacketTypeString( pIncomingPacket->type ) ) );
            status = processRemainingLength( pBuffer,
                                             pIndex,
                                             pIncomingPacket );
        }
        else
        {
            LogError( ( "Incoming packet invalid: Packet type=%u.",
                        ( unsigned int ) pIncomingPacket->type ) );
            status = MQTTBadResponse;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_InitConnect( MQTTConnectionProperties_t * pConnectProperties )
{
    MQTTStatus_t status = MQTTSuccess;

    if( pConnectProperties == NULL )
    {
        LogError( ( "pConnectProperties cannot be NULL." ) );
        status = MQTTBadParameter;
    }
    else
    {
        pConnectProperties->receiveMax = UINT16_MAX;
        pConnectProperties->maxPacketSize = MQTT_MAX_PACKET_SIZE;
        pConnectProperties->requestProblemInfo = true;
        pConnectProperties->serverReceiveMax = UINT16_MAX;
        pConnectProperties->serverMaxQos = 2U;
        pConnectProperties->serverMaxPacketSize = MQTT_MAX_PACKET_SIZE;
        pConnectProperties->isWildcardAvailable = 1U;
        pConnectProperties->isSubscriptionIdAvailable = 1U;
        pConnectProperties->isSharedAvailable = 1U;
        pConnectProperties->sessionExpiry = 0U;
        pConnectProperties->topicAliasMax = 0U;
        pConnectProperties->requestResponseInfo = false;
        pConnectProperties->retainAvailable = 1U;
        pConnectProperties->serverTopicAliasMax = 0U;
        pConnectProperties->serverKeepAlive = UINT16_MAX;
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTTPropertyBuilder_Init( MQTTPropBuilder_t * pPropertyBuilder,
                                       uint8_t * buffer,
                                       size_t length )
{
    MQTTStatus_t status = MQTTSuccess;

    if( ( pPropertyBuilder == NULL ) || ( buffer == NULL ) || ( length == 0U ) )
    {
        LogError( ( "Invalid arguments passed to MQTTPropertyBuilder_Init. "
                    "pPropertyBuilder must be non-NULL; "
                    "buffer must be non-NULL; "
                    "and length must be non-zero. " ) );
        status = MQTTBadParameter;
    }
    else if( length >= MQTT_REMAINING_LENGTH_INVALID )
    {
        LogError( ( "The length must be less than max MQTT packet size (268435456)." ) );
        status = MQTTBadParameter;
    }
    else
    {
        /* Nothing to do. All values are valid. */
    }

    if( status == MQTTSuccess )
    {
        pPropertyBuilder->pBuffer = buffer;
        pPropertyBuilder->currentIndex = 0;
        pPropertyBuilder->bufferLength = length;
        pPropertyBuilder->fieldSet = 0; /* 0 means no field is set. */
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_ValidateWillProperties( const MQTTPropBuilder_t * pPropertyBuilder )
{
    MQTTStatus_t status = MQTTSuccess;
    uint32_t propertyLength = 0U;
    uint8_t * pIndex = NULL;
    uint32_t propertyBitMask = 0;

    if( ( pPropertyBuilder == NULL ) || ( pPropertyBuilder->pBuffer == NULL ) )
    {
        status = MQTTBadParameter;
    }
    else if( ( CHECK_SIZE_T_OVERFLOWS_32BIT( pPropertyBuilder->currentIndex ) ) ||
             ( pPropertyBuilder->currentIndex >= MQTT_REMAINING_LENGTH_INVALID ) )
    {
        LogError( ( "Property length cannot have more than %" PRIu32 " bytes", MQTT_REMAINING_LENGTH_INVALID ) );
        status = MQTTBadParameter;
    }
    else
    {
        propertyLength = ( uint32_t ) pPropertyBuilder->currentIndex;
        pIndex = pPropertyBuilder->pBuffer;
    }

    while( ( propertyLength > 0U ) && ( status == MQTTSuccess ) )
    {
        uint8_t propertyId = *pIndex;
        bool used = false;
        const char * data;
        size_t dataLength;

        pIndex = &pIndex[ 1 ];
        propertyLength -= 1U;

        switch( propertyId )
        {
            case MQTT_WILL_DELAY_ID:

                if( UINT32_CHECK_BIT( propertyBitMask, MQTT_WILL_DELAY_POS ) != true )
                {
                    status = decodeUint32t( NULL, &propertyLength, &used, &pIndex );
                    UINT32_SET_BIT( propertyBitMask, MQTT_WILL_DELAY_POS );
                }
                else
                {
                    LogError( ( "Will Delay Interval included more than once in the properties." ) );
                    status = MQTTBadResponse;
                }

                break;

            case MQTT_PAYLOAD_FORMAT_ID:
               {
                   uint8_t property;

                   if( UINT32_CHECK_BIT( propertyBitMask, MQTT_PAYLOAD_FORMAT_INDICATOR_POS ) != true )
                   {
                       status = decodeUint8t( &property, &propertyLength, &used, &pIndex );
                       UINT32_SET_BIT( propertyBitMask, MQTT_PAYLOAD_FORMAT_INDICATOR_POS );
                   }
                   else
                   {
                       LogError( ( "Payload format indicator included more than once in the properties." ) );
                       status = MQTTBadResponse;
                   }

                   if( status == MQTTSuccess )
                   {
                       if( property > 1U )
                       {
                           LogError( ( "Payload Format can only be 0 or 1 in will properties." ) );
                           status = MQTTBadResponse;
                       }
                   }
               }
               break;

            case MQTT_MSG_EXPIRY_ID:

                if( UINT32_CHECK_BIT( propertyBitMask, MQTT_MESSAGE_EXPIRY_INTERVAL_POS ) != true )
                {
                    status = decodeUint32t( NULL, &propertyLength, &used, &pIndex );
                    UINT32_SET_BIT( propertyBitMask, MQTT_MESSAGE_EXPIRY_INTERVAL_POS );
                }
                else
                {
                    LogError( ( "Message Expiry Interval included more than once in the properties." ) );
                    status = MQTTBadResponse;
                }

                break;

            case MQTT_CONTENT_TYPE_ID:

                if( UINT32_CHECK_BIT( propertyBitMask, MQTT_CONTENT_TYPE_POS ) != true )
                {
                    status = decodeUtf8( &data, &dataLength, &propertyLength, &used, &pIndex );
                    UINT32_SET_BIT( propertyBitMask, MQTT_CONTENT_TYPE_POS );
                }
                else
                {
                    LogError( ( "Content Type included more than once in the properties." ) );
                    status = MQTTBadResponse;
                }

                break;

            case MQTT_RESPONSE_TOPIC_ID:

                if( UINT32_CHECK_BIT( propertyBitMask, MQTT_RESPONSE_TOPIC_POS ) != true )
                {
                    status = decodeUtf8( &data, &dataLength, &propertyLength, &used, &pIndex );
                    UINT32_SET_BIT( propertyBitMask, MQTT_RESPONSE_TOPIC_POS );
                }
                else
                {
                    LogError( ( "Response topic included more than once in the properties." ) );
                    status = MQTTBadResponse;
                }

                break;

            case MQTT_CORRELATION_DATA_ID:

                if( UINT32_CHECK_BIT( propertyBitMask, MQTT_CORRELATION_DATA_POS ) != true )
                {
                    status = decodeUtf8( &data, &dataLength, &propertyLength, &used, &pIndex );
                    UINT32_SET_BIT( propertyBitMask, MQTT_CORRELATION_DATA_POS );
                }
                else
                {
                    LogError( ( "Corelation Data included more than once in the properties." ) );
                    status = MQTTBadResponse;
                }

                break;

            case MQTT_USER_PROPERTY_ID:
               {
                   const char * key, * value;
                   size_t keyLength, valueLength;
                   status = decodeUserProp( &key,
                                            &keyLength,
                                            &value,
                                            &valueLength,
                                            &propertyLength,
                                            &pIndex );
               }
               break;

            default:
                status = MQTTBadResponse;
                break;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

/**
 * @brief Check that a property has not been seen before, then decode it.
 * Returns MQTTBadResponse if the property appears more than once.
 */
static MQTTStatus_t checkOnce( uint32_t * pBitMask,
                               uint8_t bitPos,
                               const char * pPropName )
{
    MQTTStatus_t status = MQTTSuccess;

    if( UINT32_CHECK_BIT( *pBitMask, bitPos ) == true )
    {
        LogError( ( "%s included more than once in the properties.", pPropName ) );
        status = MQTTBadResponse;
    }
    else
    {
        ( void ) pPropName;
        UINT32_SET_BIT( *pBitMask, bitPos );
    }

    return status;
}

/**
 * @brief Decode and validate a single CONNECT property.
 */
static MQTTStatus_t validateConnectProperty( uint8_t propertyId,
                                             uint32_t * pPropertyLength,
                                             uint8_t ** ppIndex,
                                             uint32_t * pBitMask,
                                             bool * pIsRequestProblemInfoSet,
                                             uint32_t * pPacketMaxSizeValue )
{
    MQTTStatus_t status = MQTTSuccess;
    bool used = false;
    const char * data;
    size_t dataLength;

    switch( propertyId )
    {
        case MQTT_SESSION_EXPIRY_ID:
            status = checkOnce( pBitMask, MQTT_SESSION_EXPIRY_INTERVAL_POS, "Session Expiry Interval" );

            if( status == MQTTSuccess )
            {
                status = decodeUint32t( NULL, pPropertyLength, &used, ppIndex );
            }

            break;

        case MQTT_RECEIVE_MAX_ID:
           {
               uint16_t receiveMax = 0U;
               status = checkOnce( pBitMask, MQTT_RECEIVE_MAXIMUM_POS, "Receive Maximum" );

               if( status == MQTTSuccess )
               {
                   status = decodeUint16t( &receiveMax, pPropertyLength, &used, ppIndex );
               }

               if( ( status == MQTTSuccess ) && ( receiveMax == 0U ) )
               {
                   LogError( ( "Receive Maximum cannot be 0 in CONNECT properties." ) );
                   status = MQTTBadResponse;
               }

               break;
           }

        case MQTT_MAX_PACKET_SIZE_ID:
           {
               uint32_t maxPacketSize = 0U;
               status = checkOnce( pBitMask, MQTT_MAX_PACKET_SIZE_POS, "Maximum Packet Size" );

               if( status == MQTTSuccess )
               {
                   status = decodeUint32t( &maxPacketSize, pPropertyLength, &used, ppIndex );
               }

               if( ( status == MQTTSuccess ) && ( maxPacketSize == 0U ) )
               {
                   LogError( ( "Maximum Packet Size cannot be 0 in CONNECT properties." ) );
                   status = MQTTBadResponse;
               }
               else if( ( status == MQTTSuccess ) && ( pPacketMaxSizeValue != NULL ) )
               {
                   *pPacketMaxSizeValue = maxPacketSize;
               }
               else
               {
                   /* Nothing to do. */
               }

               break;
           }

        case MQTT_TOPIC_ALIAS_MAX_ID:
            status = checkOnce( pBitMask, MQTT_TOPIC_ALIAS_MAX_POS, "Topic Alias Maximum" );

            if( status == MQTTSuccess )
            {
                status = decodeUint16t( NULL, pPropertyLength, &used, ppIndex );
            }

            break;

        case MQTT_REQUEST_RESPONSE_ID:
           {
               uint8_t requestResponseInfo = 0U;
               status = checkOnce( pBitMask, MQTT_REQUEST_RESPONSE_INFO_POS, "Request Response Information" );

               if( status == MQTTSuccess )
               {
                   status = decodeUint8t( &requestResponseInfo, pPropertyLength, &used, ppIndex );
               }

               if( ( status == MQTTSuccess ) && ( requestResponseInfo != 0U ) && ( requestResponseInfo != 1U ) )
               {
                   LogError( ( "Request Response Information can only be 0 or 1 in CONNECT properties." ) );
                   status = MQTTBadResponse;
               }

               break;
           }

        case MQTT_REQUEST_PROBLEM_ID:
           {
               uint8_t requestProblemInfo = 0U;
               status = checkOnce( pBitMask, MQTT_REQUEST_PROBLEM_INFO_POS, "Request Problem Information" );

               if( status == MQTTSuccess )
               {
                   status = decodeUint8t( &requestProblemInfo, pPropertyLength, &used, ppIndex );
               }

               if( ( status == MQTTSuccess ) && ( requestProblemInfo != 0U ) && ( requestProblemInfo != 1U ) )
               {
                   LogError( ( "Request Problem Information can only be 0 or 1 in CONNECT properties." ) );
                   status = MQTTBadResponse;
               }
               else if( status == MQTTSuccess )
               {
                   *pIsRequestProblemInfoSet = ( requestProblemInfo == 1U );
               }
               else
               {
                   /* Nothing to do. */
               }

               break;
           }

        case MQTT_AUTH_METHOD_ID:
            status = checkOnce( pBitMask, MQTT_AUTHENTICATION_METHOD_POS, "Authentication Method" );

            if( status == MQTTSuccess )
            {
                status = decodeUtf8( &data, &dataLength, pPropertyLength, &used, ppIndex );
            }

            break;

        case MQTT_AUTH_DATA_ID:
            status = checkOnce( pBitMask, MQTT_AUTHENTICATION_DATA_POS, "Authentication Data" );

            if( status == MQTTSuccess )
            {
                status = decodeUtf8( &data, &dataLength, pPropertyLength, &used, ppIndex );
            }

            break;

        case MQTT_USER_PROPERTY_ID:
           {
               const char * key;
               const char * value;
               size_t keyLength;
               size_t valueLength;
               status = decodeUserProp( &key, &keyLength, &value, &valueLength,
                                        pPropertyLength, ppIndex );
           }
           break;

        default:
            LogError( ( "Invalid property ID 0x%02x in CONNECT properties.", propertyId ) );
            status = MQTTBadResponse;
            break;
    }

    return status;
}

MQTTStatus_t MQTT_ValidateConnectProperties( const MQTTPropBuilder_t * pPropertyBuilder,
                                             bool * isRequestProblemInfoSet,
                                             uint32_t * pPacketMaxSizeValue )
{
    MQTTStatus_t status = MQTTSuccess;
    uint32_t propertyLength = 0U;
    uint8_t * pIndex = NULL;
    uint32_t propertyBitMask = 0;

    if( ( pPropertyBuilder == NULL ) ||
        ( pPropertyBuilder->pBuffer == NULL ) ||
        ( isRequestProblemInfoSet == NULL ) )
    {
        status = MQTTBadParameter;
    }
    else if( ( CHECK_SIZE_T_OVERFLOWS_32BIT( pPropertyBuilder->currentIndex ) ) ||
             ( pPropertyBuilder->currentIndex >= MQTT_REMAINING_LENGTH_INVALID ) )
    {
        LogError( ( "Property length cannot have more than %" PRIu32 " bytes", MQTT_REMAINING_LENGTH_INVALID ) );
        status = MQTTBadParameter;
    }
    else
    {
        propertyLength = ( uint32_t ) pPropertyBuilder->currentIndex;
        pIndex = pPropertyBuilder->pBuffer;
        *isRequestProblemInfoSet = false;
    }

    while( ( propertyLength > 0U ) && ( status == MQTTSuccess ) )
    {
        uint8_t propertyId = *pIndex;

        pIndex = &pIndex[ 1 ];
        propertyLength -= 1U;

        status = validateConnectProperty( propertyId, &propertyLength, &pIndex,
                                          &propertyBitMask, isRequestProblemInfoSet,
                                          pPacketMaxSizeValue );
    }

    if( status == MQTTSuccess )
    {
        if( ( UINT32_CHECK_BIT( propertyBitMask, MQTT_AUTHENTICATION_DATA_POS ) == true ) &&
            ( UINT32_CHECK_BIT( propertyBitMask, MQTT_AUTHENTICATION_METHOD_POS ) != true ) )
        {
            LogError( ( "Authentication data added but no authentication method present in CONNECT properties." ) );
            status = MQTTBadParameter;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_ValidateSubscribeProperties( bool isSubscriptionIdAvailable,
                                               const MQTTPropBuilder_t * propBuilder )
{
    MQTTStatus_t status = MQTTSuccess;
    uint32_t propertyLength = 0U;
    uint8_t * pLocalIndex = NULL;
    uint32_t subscriptionId = 0;
    bool subscriptionIDIncluded = false;

    if( ( propBuilder == NULL ) || ( propBuilder->pBuffer == NULL ) )
    {
        status = MQTTBadParameter;
    }
    else if( ( CHECK_SIZE_T_OVERFLOWS_32BIT( propBuilder->currentIndex ) ) ||
             ( propBuilder->currentIndex >= MQTT_REMAINING_LENGTH_INVALID ) )
    {
        LogError( ( "Property length cannot have more than %" PRIu32 " bytes", MQTT_REMAINING_LENGTH_INVALID ) );
        status = MQTTBadParameter;
    }
    else
    {
        propertyLength = ( uint32_t ) propBuilder->currentIndex;
        pLocalIndex = propBuilder->pBuffer;
    }

    while( ( propertyLength > 0U ) && ( status == MQTTSuccess ) )
    {
        uint8_t propertyId = *pLocalIndex;
        pLocalIndex = &pLocalIndex[ 1 ];
        propertyLength -= 1U;

        switch( propertyId )
        {
            case MQTT_SUBSCRIPTION_ID_ID:

                if( subscriptionIDIncluded == true )
                {
                    status = MQTTBadParameter;
                    LogError( ( "Subscription ID included. Protocol Error to include twice." ) );
                }

                if( status == MQTTSuccess )
                {
                    status = decodeVariableLength( pLocalIndex, ( size_t ) propertyLength, &subscriptionId );
                }

                if( status == MQTTSuccess )
                {
                    propertyLength -= variableLengthEncodedSize( subscriptionId );

                    if( isSubscriptionIdAvailable == false )
                    {
                        LogError( ( "Protocol Error : Subscription Id not available" ) );
                        status = MQTTBadParameter;
                    }
                    else if( subscriptionId == 0U )
                    {
                        LogError( ( "Protocol Error : Subscription Id value set to 0" ) );
                        status = MQTTBadParameter;
                    }
                    else
                    {
                        subscriptionIDIncluded = true;
                        LogTrace( ( "Processing subscription ID %" PRIu32,
                                    subscriptionId ) );
                    }
                }

                break;

            case MQTT_USER_PROPERTY_ID:
               {
                   const char * key, * value;
                   size_t keyLength, valueLength;
                   status = decodeUserProp( &key, &keyLength, &value, &valueLength, &propertyLength, &pLocalIndex );

                   if( status == MQTTSuccess )
                   {
                       LogTrace( ( "Processing User Property %.*s:%.*s",
                                   ( int ) keyLength, key,
                                   ( int ) valueLength, value ) );
                   }
               }
               break;

            default:
                status = MQTTBadParameter;
                break;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_ValidatePublishProperties( uint16_t serverTopicAliasMax,
                                             const MQTTPropBuilder_t * propBuilder,
                                             uint16_t * topicAlias )
{
    MQTTStatus_t status = MQTTSuccess;
    uint32_t propertyLength = 0U;
    uint8_t * pLocalIndex = NULL;
    bool topicAliasBool = false;

    if( ( propBuilder == NULL ) || ( propBuilder->pBuffer == NULL ) )
    {
        LogError( ( "Property Builder is NULL." ) );
        status = MQTTBadParameter;
    }
    else if( topicAlias == NULL )
    {
        LogError( ( "Topic Alias is NULL." ) );
        status = MQTTBadParameter;
    }
    else if( ( CHECK_SIZE_T_OVERFLOWS_32BIT( propBuilder->currentIndex ) ) ||
             ( propBuilder->currentIndex >= MQTT_REMAINING_LENGTH_INVALID ) )
    {
        LogError( ( "Property length cannot have more than %" PRIu32 " bytes", MQTT_REMAINING_LENGTH_INVALID ) );
        status = MQTTBadParameter;
    }
    else
    {
        propertyLength = ( uint32_t ) propBuilder->currentIndex;
        pLocalIndex = propBuilder->pBuffer;
    }

    while( ( propertyLength > 0U ) && ( status == MQTTSuccess ) )
    {
        uint8_t propertyId = *pLocalIndex;
        bool used = false;
        pLocalIndex = &pLocalIndex[ 1 ];
        propertyLength -= 1U;

        switch( propertyId )
        {
            case MQTT_PAYLOAD_FORMAT_ID:
               {
                   uint8_t property;
                   status = decodeUint8t( &property, &propertyLength, &used, &pLocalIndex );
               }
               break;

            case MQTT_MSG_EXPIRY_ID:
               {
                   uint32_t property;
                   status = decodeUint32t( &property, &propertyLength, &used, &pLocalIndex );
                   break;
               }

            case MQTT_CONTENT_TYPE_ID:
            case MQTT_CORRELATION_DATA_ID:
            case MQTT_RESPONSE_TOPIC_ID:
               {
                   const char * pProperty;
                   size_t length;
                   status = decodeUtf8( &pProperty, &length, &propertyLength, &used, &pLocalIndex );
                   break;
               }

            case MQTT_TOPIC_ALIAS_ID:
                status = decodeUint16t( topicAlias, &propertyLength, &topicAliasBool, &pLocalIndex );

                if( ( status == MQTTSuccess ) && ( serverTopicAliasMax < *topicAlias ) )
                {
                    LogError( ( "Protocol Error: Topic Alias greater than Topic Alias Max" ) );
                    status = MQTTBadParameter;
                }

                break;

            case MQTT_USER_PROPERTY_ID:
               {
                   const char * pPropertyKey;
                   size_t propertyKeyLen;
                   const char * pPropertyValue;
                   size_t propertyValueLen;
                   status = decodeUserProp( &pPropertyKey,
                                            &propertyKeyLen,
                                            &pPropertyValue,
                                            &propertyValueLen,
                                            &propertyLength,
                                            &pLocalIndex );
               }
               break;

            default:
                status = MQTTBadParameter;
                break;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_ValidatePublishParams( const MQTTPublishInfo_t * pPublishInfo,
                                         uint8_t retainAvailable,
                                         uint8_t maxQos,
                                         uint16_t topicAlias,
                                         uint32_t maxPacketSize )
{
    MQTTStatus_t status;

    if( pPublishInfo == NULL )
    {
        LogError( ( "Argument cannot be NULL: pPublishInfo=%p ",
                    ( const void * ) pPublishInfo ) );
        status = MQTTBadParameter;
    }
    else if( ( pPublishInfo->retain == true ) && ( retainAvailable == 0U ) )
    {
        LogError( ( "Retain is not available." ) );
        status = MQTTBadParameter;
    }
    else if( ( pPublishInfo->qos != MQTTQoS0 ) && ( maxQos == 0U ) )
    {
        LogError( ( "Qos value = %hu is not allowed by the server ",
                    ( unsigned short ) pPublishInfo->qos ) );
        status = MQTTBadParameter;
    }
    else if( ( topicAlias == 0U ) && ( pPublishInfo->topicNameLength == 0U ) )
    {
        LogError( ( "Invalid topic name for PUBLISH: pTopicName=%p, "
                    "topicNameLength=%hu.",
                    ( const void * ) pPublishInfo->pTopicName,
                    ( unsigned short ) pPublishInfo->topicNameLength ) );
        status = MQTTBadParameter;
    }
    else if( ( pPublishInfo->pTopicName == NULL ) && ( pPublishInfo->topicNameLength != 0U ) )
    {
        LogError( ( "Invalid topic name for PUBLISH: pTopicName=%p, "
                    "topicNameLength=%hu.",
                    ( const void * ) pPublishInfo->pTopicName,
                    ( unsigned short ) pPublishInfo->topicNameLength ) );
        status = MQTTBadParameter;
    }
    else if( CHECK_SIZE_T_OVERFLOWS_16BIT( pPublishInfo->topicNameLength ) )
    {
        LogError( ( "topicNameLength must be less than 65535 to fit in 16-bits." ) );
        status = MQTTBadParameter;
    }
    else if( maxPacketSize == 0U )
    {
        status = MQTTBadParameter;
    }
    else
    {
        status = MQTTSuccess;
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_ValidatePublishAckProperties( const MQTTPropBuilder_t * pPropertyBuilder )
{
    MQTTStatus_t status = MQTTSuccess;
    uint32_t propertyLength = 0U;
    uint8_t * pIndex = NULL;
    bool used = false;

    if( ( pPropertyBuilder != NULL ) &&
        ( ( CHECK_SIZE_T_OVERFLOWS_32BIT( pPropertyBuilder->currentIndex ) ) ||
          ( pPropertyBuilder->currentIndex >= MQTT_REMAINING_LENGTH_INVALID ) ) )
    {
        LogError( ( "Property length cannot have more than %" PRIu32 " bytes", MQTT_REMAINING_LENGTH_INVALID ) );
        status = MQTTBadParameter;
    }

    if( ( status == MQTTSuccess ) && ( pPropertyBuilder != NULL ) && ( pPropertyBuilder->pBuffer != NULL ) )
    {
        propertyLength = ( uint32_t ) pPropertyBuilder->currentIndex;
        pIndex = pPropertyBuilder->pBuffer;
    }

    while( ( propertyLength > 0U ) && ( status == MQTTSuccess ) )
    {
        uint8_t propertyId = *pIndex;
        pIndex = &pIndex[ 1 ];
        propertyLength -= 1U;

        switch( propertyId )
        {
            case MQTT_REASON_STRING_ID:
               {
                   const char * pProperty;
                   size_t length;
                   status = decodeUtf8( &pProperty, &length, &propertyLength, &used, &pIndex );
               }
               break;

            case MQTT_USER_PROPERTY_ID:
               {
                   const char * key, * value;
                   size_t keyLength, valueLength;
                   status = decodeUserProp( &key,
                                            &keyLength,
                                            &value,
                                            &valueLength,
                                            &propertyLength,
                                            &pIndex );
               }
               break;

            default:
                status = MQTTBadParameter;
                break;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_GetAckPacketSize( uint32_t * pRemainingLength,
                                    uint32_t * pPacketSize,
                                    uint32_t maxPacketSize,
                                    size_t ackPropertyLength )
{
    MQTTStatus_t status = MQTTSuccess;
    uint32_t length = 0U;
    uint32_t propertyLength;
    uint32_t packetSize = 0U;

    /* Validate the parameters. */
    if( ( pRemainingLength == NULL ) || ( pPacketSize == NULL ) )
    {
        LogError( ( "pRemainingLength and pPacketSize cannot be NULL." ) );
        status = MQTTBadParameter;
    }
    else if( maxPacketSize == 0U )
    {
        LogError( ( "maxPacketSize cannot be 0 as specified by MQTT spec." ) );
        status = MQTTBadParameter;
    }
    else if( CHECK_SIZE_T_OVERFLOWS_32BIT( ackPropertyLength ) ||
             ( ackPropertyLength > MQTT_MAX_REMAINING_LENGTH ) )
    {
        LogError( ( "ackPropertyLength must be smaller than 268435455 to fit in MQTT packet." ) );
        status = MQTTBadParameter;
    }
    else
    {
        propertyLength = ( uint32_t ) ackPropertyLength;

        /* 1 byte Reason code + 2 byte Packet Identifier. */
        length += 3U;

        length += variableLengthEncodedSize( propertyLength ) + propertyLength;

        if( length > MQTT_MAX_REMAINING_LENGTH )
        {
            status = MQTTBadParameter;
            LogError( ( "Remaining Length greater than Maximum Remaining Length according to MQTTv5 spec." ) );
        }
        else
        {
            *pRemainingLength = length;
        }
    }

    if( status == MQTTSuccess )
    {
        /* Length of variable header + 1 byte ACK header +
         * bytes required to encode the remaining length. */
        packetSize = length + 1U + variableLengthEncodedSize( length );

        if( packetSize > maxPacketSize )
        {
            status = MQTTBadParameter;
            LogError( ( "Packet size greater than Max Packet Size specified in the CONNACK" ) );
        }
        else
        {
            *pPacketSize = packetSize;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_ValidateDisconnectProperties( uint32_t connectSessionExpiry,
                                                const MQTTPropBuilder_t * pPropertyBuilder )
{
    MQTTStatus_t status = MQTTSuccess;
    uint32_t propertyLength = 0U;
    uint8_t * pIndex = NULL;
    uint32_t sessionExpiry;

    if( ( pPropertyBuilder == NULL ) || ( pPropertyBuilder->pBuffer == NULL ) )
    {
        LogError( ( "Arguments cannot be NULL : pPropertyBuilder=%p.", ( const void * ) pPropertyBuilder ) );
        status = MQTTBadParameter;
    }
    else if( ( CHECK_SIZE_T_OVERFLOWS_32BIT( pPropertyBuilder->currentIndex ) ) ||
             ( pPropertyBuilder->currentIndex >= MQTT_REMAINING_LENGTH_INVALID ) )
    {
        LogError( ( "Property length cannot have more than %" PRIu32 " bytes", MQTT_REMAINING_LENGTH_INVALID ) );
        status = MQTTBadParameter;
    }
    else
    {
        propertyLength = ( uint32_t ) pPropertyBuilder->currentIndex;
        pIndex = pPropertyBuilder->pBuffer;
    }

    while( ( propertyLength > 0U ) && ( status == MQTTSuccess ) )
    {
        uint8_t propertyId = *pIndex;
        bool used = false;
        pIndex = &pIndex[ 1 ];
        propertyLength -= 1U;

        switch( propertyId )
        {
            case MQTT_SESSION_EXPIRY_ID:
                status = decodeUint32t( &sessionExpiry, &propertyLength, &used, &pIndex );

                if( status == MQTTSuccess )
                {
                    if( ( connectSessionExpiry == 0U ) && ( sessionExpiry != 0U ) )
                    {
                        status = MQTTBadParameter;
                        LogError( ( "Disconnect Session Expiry non-zero while Connect Session Expiry was zero. " ) );
                    }
                }

                break;

            case MQTT_REASON_STRING_ID:
               {
                   const char * pProperty;
                   size_t length;
                   status = decodeUtf8( &pProperty, &length, &propertyLength, &used, &pIndex );
               }
               break;

            case MQTT_USER_PROPERTY_ID:
               {
                   const char * key, * value;
                   size_t keyLength, valueLength;
                   status = decodeUserProp( &key, &keyLength, &value, &valueLength, &propertyLength, &pIndex );
               }
               break;

            default:
                status = MQTTBadParameter;
                break;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_DeserializeDisconnect( const MQTTPacketInfo_t * pPacket,
                                         uint32_t maxPacketSize,
                                         MQTTReasonCodeInfo_t * pDisconnectInfo,
                                         MQTTPropBuilder_t * pPropBuffer )
{
    MQTTStatus_t status = MQTTSuccess;
    uint8_t * pIndex = NULL;
    uint32_t propertyLength = 0U;

    /* Validate the arguments. */
    if( ( pPacket == NULL ) || ( pPacket->pRemainingData == NULL ) )
    {
        LogError( ( "pPacket and pPacket->pRemainingData must not be NULL." ) );
        status = MQTTBadParameter;
    }
    else if( pDisconnectInfo == NULL )
    {
        LogError( ( "pDisconnectInfo must not be NULL." ) );
        status = MQTTBadParameter;
    }
    else if( maxPacketSize == 0U )
    {
        LogError( ( "maxPacketSize must not be 0." ) );
        status = MQTTBadParameter;
    }
    else if( pPacket->remainingLength >= MQTT_REMAINING_LENGTH_INVALID )
    {
        LogError( ( "pPacket->remainingLength must be less than 268435456." ) );
        status = MQTTBadResponse;
    }
    else if( CHECK_U32T_OVERFLOWS_SIZE_T( pPacket->remainingLength ) )
    {
        LogError( ( "pPacket->remainingLength cannot fit in size_t." ) );

        /* More details at: https://github.com/FreeRTOS/coreMQTT/blob/main/MISRA.md#rule-143 */
        /* coverity[misra_c_2012_rule_14_3_violation] */
        status = MQTTBadParameter;
    }

    /* Packet size should not be more than the max allowed by the client.
     * The length is calculated as: Remaining length +
     *       Bytes required to encode the remaining length +
     *       The disconnect header of 1 byte.
     */
    else if( ( pPacket->remainingLength + variableLengthEncodedSize( pPacket->remainingLength ) + 1U ) > maxPacketSize )
    {
        status = MQTTBadResponse;
    }
    else if( pPacket->remainingLength == 0U )
    {
        /* No properties or reason code provided. Nothing to do. */
    }
    else
    {
        /* Extract the reason code. */
        pIndex = pPacket->pRemainingData;
        pDisconnectInfo->reasonCode = pIndex;
        pDisconnectInfo->reasonCodeLength = 1U;
        pIndex++;

        /* Validate the reason code. */
        /* More details at: https://github.com/FreeRTOS/coreMQTT/blob/main/MISRA.md#rule-105 */
        /* coverity[misra_c_2012_rule_10_5_violation] */
        status = validateDisconnectResponse( ( MQTTSuccessFailReasonCode_t ) ( *pDisconnectInfo->reasonCode ), true );
    }

    if( status == MQTTSuccess )
    {
        if( ( pPacket->remainingLength > 1U ) )
        {
            /* Extract the property length. */
            /* More details at: https://github.com/FreeRTOS/coreMQTT/blob/main/MISRA.md#rule-108 */
            /* coverity[misra_c_2012_rule_10_8_violation] */
            status = decodeVariableLength( pIndex, ( size_t ) ( pPacket->remainingLength - 1U ), &propertyLength );

            if( status == MQTTSuccess )
            {
                /* Validate the remaining length. It must only have the reason code
                 * and the properties and the bytes needed to encode the property length. */
                if( pPacket->remainingLength != ( propertyLength + variableLengthEncodedSize( propertyLength ) + 1U ) )
                {
                    LogError( ( "Remaining length doesn't match the expected size." ) );
                    status = MQTTBadResponse;
                }
                else if( CHECK_U32T_OVERFLOWS_SIZE_T( propertyLength ) )
                {
                    LogError( ( "Incoming property length will overflow the property buffer." ) );

                    /* More details at: https://github.com/FreeRTOS/coreMQTT/blob/main/MISRA.md#rule-143 */
                    /* coverity[misra_c_2012_rule_14_3_violation] */
                    status = MQTTBadResponse;
                }
                else
                {
                    pIndex = &pIndex[ ( size_t ) variableLengthEncodedSize( propertyLength ) ];

                    if( pPropBuffer != NULL )
                    {
                        pPropBuffer->bufferLength = propertyLength;
                        pPropBuffer->pBuffer = pIndex;
                    }
                }
            }
            else
            {
                LogError( ( "Failed to decode the property length. Malformed packet." ) );
                status = MQTTBadResponse;
            }
        }
    }

    if( status == MQTTSuccess )
    {
        status = validateIncomingDisconnectProperties( pIndex, propertyLength );

        if( status != MQTTSuccess )
        {
            LogError( ( "Failed to validate disconnect properties." ) );
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t validateIncomingDisconnectProperties( uint8_t * pIndex,
                                                          uint32_t disconnectPropertyLength )
{
    MQTTStatus_t status = MQTTSuccess;
    uint8_t * pLocalIndex = pIndex;
    const char * pReasonString;
    size_t reasonStringLength;
    const char * pServerRef;
    size_t pServerRefLength;
    uint32_t propertyLength = disconnectPropertyLength;
    bool reasonString = false;
    bool serverRef = false;

    while( ( propertyLength > 0U ) && ( status == MQTTSuccess ) )
    {
        /* Decode the property id. */
        uint8_t propertyId = *pLocalIndex;
        pLocalIndex = &pLocalIndex[ 1 ];
        propertyLength -= 1U;

        /* Validate the property id and decode accordingly. */
        switch( propertyId )
        {
            case MQTT_REASON_STRING_ID:
                status = decodeUtf8( &pReasonString, &reasonStringLength, &propertyLength, &reasonString, &pLocalIndex );
                break;

            case MQTT_USER_PROPERTY_ID:
               {
                   const char * key, * value;
                   size_t keyLength, valueLength;
                   status = decodeUserProp( &key, &keyLength, &value, &valueLength, &propertyLength, &pLocalIndex );
               }
               break;

            case MQTT_SERVER_REF_ID:
                status = decodeUtf8( &pServerRef, &pServerRefLength, &propertyLength, &serverRef, &pLocalIndex );
                break;

            default:
                status = MQTTBadResponse;
                break;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

// === source/core_mqtt_state.c (verbatim from upstream) ===
/*
 * coreMQTT
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

/**
 * @file core_mqtt_state.c
 * @brief Implements the functions in core_mqtt_state.h.
 */
#include <assert.h>
#include <string.h>

/* Include config defaults header to get default values of configs. */

/*-----------------------------------------------------------*/

/**
 * @brief A global static variable used to generate the macro
 * #MQTT_INVALID_STATE_COUNT of size_t length.
 */
static const size_t ZERO_SIZE_T = 0U;

/**
 * @brief This macro depicts the invalid value for the state publishes.
 */
#define MQTT_INVALID_STATE_COUNT    ( ~ZERO_SIZE_T )

/**
 * @brief Create a 16-bit bitmap with bit set at specified position.
 *
 * @param[in] position The position at which the bit need to be set.
 */
#define UINT16_BITMAP_BIT_SET_AT( position )    ( ( uint16_t ) 0x01U << ( ( uint16_t ) position ) )

/**
 * @brief Set a bit in an 16-bit unsigned integer.
 *
 * @param[in] x The 16-bit unsigned integer to set a bit.
 * @param[in] position The position at which the bit need to be set.
 */
#define UINT16_SET_BIT( x, position )           ( ( x ) = ( uint16_t ) ( ( x ) | ( UINT16_BITMAP_BIT_SET_AT( position ) ) ) )

/**
 * @brief Macro for checking if a bit is set in a 16-bit unsigned integer.
 *
 * @param[in] x The unsigned 16-bit integer to check.
 * @param[in] position Which bit to check.
 */
#define UINT16_CHECK_BIT( x, position )         ( ( ( x ) & ( UINT16_BITMAP_BIT_SET_AT( position ) ) ) == ( UINT16_BITMAP_BIT_SET_AT( position ) ) )

/*-----------------------------------------------------------*/

/**
 * @brief Test if a transition to new state is possible, when dealing with PUBLISHes.
 *
 * @param[in] currentState The current state.
 * @param[in] newState State to transition to.
 * @param[in] opType Reserve, Send, or Receive.
 * @param[in] qos 0, 1, or 2.
 *
 * @note This function does not validate the current state, or the new state
 * based on either the operation type or QoS. It assumes the new state is valid
 * given the opType and QoS, which will be the case if calculated by
 * MQTT_CalculateStatePublish().
 *
 * @return `true` if transition is possible, else `false`
 */
static bool validateTransitionPublish( MQTTPublishState_t currentState,
                                       MQTTPublishState_t newState,
                                       MQTTStateOperation_t opType,
                                       MQTTQoS_t qos );

/**
 * @brief Test if a transition to a new state is possible, when dealing with acks.
 *
 * @param[in] currentState The current state.
 * @param[in] newState State to transition to.
 *
 * @return `true` if transition is possible, else `false`.
 */
static bool validateTransitionAck( MQTTPublishState_t currentState,
                                   MQTTPublishState_t newState );

/**
 * @brief Test if the publish corresponding to an ack is outgoing or incoming.
 *
 * @param[in] packetType PUBACK, PUBREC, PUBREL, or PUBCOMP.
 * @param[in] opType Send, or Receive.
 *
 * @return `true` if corresponds to outgoing publish, else `false`.
 */
static bool isPublishOutgoing( MQTTPubAckType_t packetType,
                               MQTTStateOperation_t opType );

/**
 * @brief Find a packet ID in the state record.
 *
 * @param[in] records State record array.
 * @param[in] recordCount Length of record array.
 * @param[in] packetId packet ID to search for.
 * @param[out] pQos QoS retrieved from record.
 * @param[out] pCurrentState state retrieved from record.
 *
 * @return index of the packet id in the record if it exists, else the record length.
 */
static size_t findInRecord( const MQTTPubAckInfo_t * records,
                            size_t recordCount,
                            uint16_t packetId,
                            MQTTQoS_t * pQos,
                            MQTTPublishState_t * pCurrentState );

/**
 * @brief Compact records.
 *
 * Records are arranged in the relative order to maintain message ordering.
 * This will lead to fragmentation and this function will help in defragmenting
 * the records array.
 *
 * @param[in] records State record array.
 * @param[in] recordCount Length of record array.
 */
static void compactRecords( MQTTPubAckInfo_t * records,
                            size_t recordCount );

/**
 * @brief Store a new entry in the state record.
 *
 * @param[in] records State record array.
 * @param[in] recordCount Length of record array.
 * @param[in] packetId Packet ID of new entry.
 * @param[in] qos QoS of new entry.
 * @param[in] publishState State of new entry.
 *
 * @return #MQTTSuccess, #MQTTNoMemory, or #MQTTStateCollision.
 */
static MQTTStatus_t addRecord( MQTTPubAckInfo_t * records,
                               size_t recordCount,
                               uint16_t packetId,
                               MQTTQoS_t qos,
                               MQTTPublishState_t publishState );

/**
 * @brief Update and possibly delete an entry in the state record.
 *
 * @param[in] records State record array.
 * @param[in] recordIndex index of record to update.
 * @param[in] newState New state to update.
 * @param[in] shouldDelete Whether an existing entry should be deleted.
 */
static void updateRecord( MQTTPubAckInfo_t * records,
                          size_t recordIndex,
                          MQTTPublishState_t newState,
                          bool shouldDelete );

/**
 * @brief Get the packet ID and index of an outgoing publish in specified
 * states.
 *
 * @param[in] pMqttContext Initialized MQTT context.
 * @param[in] searchStates The states to search for in 2-byte bit map.
 * @param[in,out] pCursor Index at which to start searching.
 *
 * @return Packet ID of the outgoing publish.
 */
static uint16_t stateSelect( const MQTTContext_t * pMqttContext,
                             uint16_t searchStates,
                             MQTTStateCursor_t * pCursor );

/**
 * @brief Update the state records for an ACK after state transition
 * validations.
 *
 * @param[in] records State records pointer.
 * @param[in] maxRecordCount The maximum number of records.
 * @param[in] recordIndex Index at which the record is stored.
 * @param[in] packetId Packet id of the packet.
 * @param[in] currentState Current state of the publish record.
 * @param[in] newState New state of the publish.
 *
 * @return #MQTTIllegalState, or #MQTTSuccess.
 */
static MQTTStatus_t updateStateAck( MQTTPubAckInfo_t * records,
                                    size_t maxRecordCount,
                                    size_t recordIndex,
                                    uint16_t packetId,
                                    MQTTPublishState_t currentState,
                                    MQTTPublishState_t newState );

/**
 * @brief Update the state record for a PUBLISH packet after validating
 * the state transitions.
 *
 * @param[in] pMqttContext Initialized MQTT context.
 * @param[in] recordIndex Index in state records at which publish record exists.
 * @param[in] packetId ID of the PUBLISH packet.
 * @param[in] opType Send or Receive.
 * @param[in] qos 0, 1, or 2.
 * @param[in] currentState Current state of the publish record.
 * @param[in] newState New state of the publish record.
 *
 * @return #MQTTIllegalState, #MQTTStateCollision or #MQTTSuccess.
 */
static MQTTStatus_t updateStatePublish( const MQTTContext_t * pMqttContext,
                                        size_t recordIndex,
                                        uint16_t packetId,
                                        MQTTStateOperation_t opType,
                                        MQTTQoS_t qos,
                                        MQTTPublishState_t currentState,
                                        MQTTPublishState_t newState );

/*-----------------------------------------------------------*/

static bool validateTransitionPublish( MQTTPublishState_t currentState,
                                       MQTTPublishState_t newState,
                                       MQTTStateOperation_t opType,
                                       MQTTQoS_t qos )
{
    bool isValid = false;

    switch( currentState )
    {
        case MQTTStateNull:

            /* Transitions from null occur when storing a new entry into the record. */
            if( opType == MQTT_RECEIVE )
            {
                isValid = ( newState == MQTTPubAckSend ) || ( newState == MQTTPubRecSend );
            }

            break;

        case MQTTPublishSend:

            /* Outgoing publish. All such publishes start in this state due to
             * the reserve operation. */
            switch( qos )
            {
                case MQTTQoS1:
                    isValid = newState == MQTTPubAckPending;
                    break;

                case MQTTQoS2:
                    isValid = newState == MQTTPubRecPending;
                    break;

                default:
                    /* QoS 0 is checked before calling this function. */
                    break;
            }

            break;

        /* Below cases are for validating the resends of publish when a session is
         * reestablished. */
        case MQTTPubAckPending:

            /* When a session is reestablished, outgoing QoS1 publishes in state
             * #MQTTPubAckPending can be resent. The state remains the same. */
            isValid = newState == MQTTPubAckPending;

            break;

        case MQTTPubRecPending:

            /* When a session is reestablished, outgoing QoS2 publishes in state
             * #MQTTPubRecPending can be resent. The state remains the same. */
            isValid = newState == MQTTPubRecPending;

            break;

        default:
            /* For a PUBLISH, we should not start from any other state. */
            break;
    }

    return isValid;
}

/*-----------------------------------------------------------*/

static bool validateTransitionAck( MQTTPublishState_t currentState,
                                   MQTTPublishState_t newState )
{
    bool isValid = false;

    switch( currentState )
    {
        case MQTTPubAckSend:
        /* Incoming publish, QoS 1. */
        case MQTTPubAckPending:
            /* Outgoing publish, QoS 1. */
            isValid = newState == MQTTPublishDone;
            break;

        case MQTTPubRecSend:
            /* Incoming publish, QoS 2. */
            isValid = newState == MQTTPubRelPending;
            break;

        case MQTTPubRelPending:

            /* Incoming publish, QoS 2.
             * There are 2 valid transitions possible.
             * 1. MQTTPubRelPending -> MQTTPubCompSend : A PUBREL ack is received
             *    when publish record state is MQTTPubRelPending. This is the
             *    normal state transition without any connection interruptions.
             * 2. MQTTPubRelPending -> MQTTPubRelPending : Receiving a duplicate
             *    QoS2 publish can result in a transition to the same state.
             *    This can happen in the below state transition.
             *    1. Incoming publish received.
             *    2. PUBREC ack sent and state is now MQTTPubRelPending.
             *    3. TCP connection failure and broker didn't receive the PUBREC.
             *    4. Reestablished MQTT session.
             *    5. MQTT broker resent the un-acked publish.
             *    6. Publish is received when publish record state is in
             *       MQTTPubRelPending.
             *    7. Sending out a PUBREC will result in this transition
             *       to the same state. */
            isValid = ( newState == MQTTPubCompSend ) ||
                      ( newState == MQTTPubRelPending );
            break;

        case MQTTPubCompSend:

            /* Incoming publish, QoS 2.
             * There are 2 valid transitions possible.
             * 1. MQTTPubCompSend -> MQTTPublishDone : A PUBCOMP ack is sent
             *    after receiving a PUBREL from broker. This is the
             *    normal state transition without any connection interruptions.
             * 2. MQTTPubCompSend -> MQTTPubCompSend : Receiving a duplicate PUBREL
             *    can result in a transition to the same state.
             *    This can happen in the below state transition.
             *    1. A TCP connection failure happened before sending a PUBCOMP
             *       for an incoming PUBREL.
             *    2. Reestablished an MQTT session.
             *    3. MQTT broker resent the un-acked PUBREL.
             *    4. Receiving the PUBREL again will result in this transition
             *       to the same state. */
            isValid = ( newState == MQTTPublishDone ) ||
                      ( newState == MQTTPubCompSend );
            break;

        case MQTTPubRecPending:
            /* Outgoing publish, Qos 2. */
            isValid = newState == MQTTPubRelSend;
            break;

        case MQTTPubRelSend:
            /* Outgoing publish, Qos 2. */
            isValid = newState == MQTTPubCompPending;
            break;

        case MQTTPubCompPending:

            /* Outgoing publish, Qos 2.
             * There are 2 valid transitions possible.
             * 1. MQTTPubCompPending -> MQTTPublishDone : A PUBCOMP is received.
             *    This marks the complete state transition for the publish packet.
             *    This is the normal state transition without any connection
             *    interruptions.
             * 2. MQTTPubCompPending -> MQTTPubCompPending : Resending a PUBREL for
             *    packets in state #MQTTPubCompPending can result in this
             *    transition to the same state.
             *    This can happen in the below state transition.
             *    1. A TCP connection failure happened before receiving a PUBCOMP
             *       for an outgoing PUBREL.
             *    2. An MQTT session is reestablished.
             *    3. Resending the un-acked PUBREL results in this transition
             *       to the same state. */
            isValid = ( newState == MQTTPublishDone ) ||
                      ( newState == MQTTPubCompPending );
            break;

        default:

            /* 1. MQTTPublishDone - state should transition to invalid since it
             *    will be removed from the record.
             * 2. MQTTPublishSend - If an ack was sent/received we shouldn't
             *    have been in this state.
             * 3. MQTTStateNull - If an ack was sent/received the record should
             *    exist.
             * 4. Any other state is invalid.
             */
            break;
    }

    return isValid;
}

/*-----------------------------------------------------------*/

static bool isPublishOutgoing( MQTTPubAckType_t packetType,
                               MQTTStateOperation_t opType )
{
    bool isOutgoing = false;

    switch( packetType )
    {
        case MQTTPuback:
        case MQTTPubrec:
        case MQTTPubcomp:
            isOutgoing = opType == MQTT_RECEIVE;
            break;

        case MQTTPubrel:
            isOutgoing = opType == MQTT_SEND;
            break;

        default:
            /* No other ack type. */
            break;
    }

    return isOutgoing;
}

/*-----------------------------------------------------------*/

static size_t findInRecord( const MQTTPubAckInfo_t * records,
                            size_t recordCount,
                            uint16_t packetId,
                            MQTTQoS_t * pQos,
                            MQTTPublishState_t * pCurrentState )
{
    size_t index = 0;

    assert( packetId != MQTT_PACKET_ID_INVALID );

    *pCurrentState = MQTTStateNull;

    for( index = 0; index < recordCount; index++ )
    {
        if( records[ index ].packetId == packetId )
        {
            *pQos = records[ index ].qos;
            *pCurrentState = records[ index ].publishState;
            break;
        }
    }

    if( index == recordCount )
    {
        index = MQTT_INVALID_STATE_COUNT;
    }

    return index;
}

/*-----------------------------------------------------------*/

static void compactRecords( MQTTPubAckInfo_t * records,
                            size_t recordCount )
{
    size_t index = 0;
    size_t emptyIndex = MQTT_INVALID_STATE_COUNT;

    assert( records != NULL );

    /* Find the empty spots and fill those with non empty values. */
    for( ; index < recordCount; index++ )
    {
        /* Find the first empty spot. */
        if( records[ index ].packetId == MQTT_PACKET_ID_INVALID )
        {
            if( emptyIndex == MQTT_INVALID_STATE_COUNT )
            {
                emptyIndex = index;
            }
        }
        else
        {
            if( emptyIndex != MQTT_INVALID_STATE_COUNT )
            {
                /* Copy over the contents at non empty index to empty index. */
                records[ emptyIndex ].packetId = records[ index ].packetId;
                records[ emptyIndex ].qos = records[ index ].qos;
                records[ emptyIndex ].publishState = records[ index ].publishState;

                /* Mark the record at current non empty index as invalid. */
                records[ index ].packetId = MQTT_PACKET_ID_INVALID;
                records[ index ].qos = MQTTQoS0;
                records[ index ].publishState = MQTTStateNull;

                /* Advance the emptyIndex. */
                emptyIndex++;
            }
        }
    }
}

/*-----------------------------------------------------------*/

static MQTTStatus_t addRecord( MQTTPubAckInfo_t * records,
                               size_t recordCount,
                               uint16_t packetId,
                               MQTTQoS_t qos,
                               MQTTPublishState_t publishState )
{
    MQTTStatus_t status = MQTTNoMemory;
    int32_t index = 0;
    size_t availableIndex = recordCount;
    bool validEntryFound = false;

    assert( packetId != MQTT_PACKET_ID_INVALID );
    assert( qos != MQTTQoS0 );

    /* Check if we have to compact the records. This is known by checking if
     * the last spot in the array is filled. */
    if( records[ recordCount - 1U ].packetId != MQTT_PACKET_ID_INVALID )
    {
        compactRecords( records, recordCount );
    }

    /* Start from end so first available index will be populated.
     * Available index is always found after the last element in the records.
     * This is to make sure the relative order of the records in order to meet
     * the message ordering requirement of MQTT spec 5.0. */
    for( index = ( ( int32_t ) recordCount - 1 ); index >= 0; index-- )
    {
        /* Available index is only found after packet at the highest index. */
        if( records[ index ].packetId == MQTT_PACKET_ID_INVALID )
        {
            if( validEntryFound == false )
            {
                availableIndex = ( size_t ) index;
            }
        }
        else
        {
            /* A non-empty spot found in the records. */
            validEntryFound = true;

            if( records[ index ].packetId == packetId )
            {
                /* Collision. */
                LogError( ( "Collision when adding PacketID=%u at index=%d.",
                            ( unsigned int ) packetId,
                            ( int ) index ) );

                status = MQTTStateCollision;
                availableIndex = recordCount;
                break;
            }
        }
    }

    if( availableIndex < recordCount )
    {
        records[ availableIndex ].packetId = packetId;
        records[ availableIndex ].qos = qos;
        records[ availableIndex ].publishState = publishState;
        status = MQTTSuccess;
    }

    return status;
}

/*-----------------------------------------------------------*/

static void updateRecord( MQTTPubAckInfo_t * records,
                          size_t recordIndex,
                          MQTTPublishState_t newState,
                          bool shouldDelete )
{
    assert( records != NULL );

    if( shouldDelete == true )
    {
        /* Mark the record as invalid. */
        records[ recordIndex ].packetId = MQTT_PACKET_ID_INVALID;
        records[ recordIndex ].qos = MQTTQoS0;
        records[ recordIndex ].publishState = MQTTStateNull;
    }
    else
    {
        records[ recordIndex ].publishState = newState;
    }
}

/*-----------------------------------------------------------*/

static uint16_t stateSelect( const MQTTContext_t * pMqttContext,
                             uint16_t searchStates,
                             MQTTStateCursor_t * pCursor )
{
    uint16_t packetId = MQTT_PACKET_ID_INVALID;
    uint16_t outgoingStates = 0U;
    const MQTTPubAckInfo_t * records = NULL;
    size_t maxCount;
    bool stateCheck = false;

    assert( pMqttContext != NULL );
    assert( searchStates != 0U );
    assert( pCursor != NULL );

    /* Create a bit map with all the outgoing publish states. */
    UINT16_SET_BIT( outgoingStates, MQTTPublishSend );
    UINT16_SET_BIT( outgoingStates, MQTTPubAckPending );
    UINT16_SET_BIT( outgoingStates, MQTTPubRecPending );
    UINT16_SET_BIT( outgoingStates, MQTTPubRelSend );
    UINT16_SET_BIT( outgoingStates, MQTTPubCompPending );

    /* Only outgoing publish records need to be searched. */
    assert( ( outgoingStates & searchStates ) > 0U );
    assert( ( ~outgoingStates & searchStates ) == 0U );

    records = pMqttContext->outgoingPublishRecords;
    maxCount = pMqttContext->outgoingPublishRecordMaxCount;

    while( *pCursor < maxCount )
    {
        /* Check if any of the search states are present. */
        stateCheck = UINT16_CHECK_BIT( searchStates, records[ *pCursor ].publishState );

        if( stateCheck == true )
        {
            packetId = records[ *pCursor ].packetId;
            ( *pCursor )++;
            break;
        }

        ( *pCursor )++;
    }

    return packetId;
}

/*-----------------------------------------------------------*/

MQTTPublishState_t MQTT_CalculateStateAck( MQTTPubAckType_t packetType,
                                           MQTTStateOperation_t opType,
                                           MQTTQoS_t qos )
{
    MQTTPublishState_t calculatedState = MQTTStateNull;
    /* There are more QoS2 cases than QoS1, so initialize to that. */
    bool qosValid = qos == MQTTQoS2;

    switch( packetType )
    {
        case MQTTPuback:
            qosValid = qos == MQTTQoS1;
            calculatedState = MQTTPublishDone;
            break;

        case MQTTPubrec:

            /* Incoming publish: send PUBREC, PUBREL pending.
             * Outgoing publish: receive PUBREC, send PUBREL. */
            calculatedState = ( opType == MQTT_SEND ) ? MQTTPubRelPending : MQTTPubRelSend;
            break;

        case MQTTPubrel:

            /* Incoming publish: receive PUBREL, send PUBCOMP.
             * Outgoing publish: send PUBREL, PUBCOMP pending. */
            calculatedState = ( opType == MQTT_SEND ) ? MQTTPubCompPending : MQTTPubCompSend;
            break;

        case MQTTPubcomp:
            calculatedState = MQTTPublishDone;
            break;

        default:
            /* No other ack type. */
            break;
    }

    /* Sanity check, make sure ack and QoS agree. */
    if( qosValid == false )
    {
        calculatedState = MQTTStateNull;
    }

    return calculatedState;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t updateStateAck( MQTTPubAckInfo_t * records,
                                    size_t maxRecordCount,
                                    size_t recordIndex,
                                    uint16_t packetId,
                                    MQTTPublishState_t currentState,
                                    MQTTPublishState_t newState )
{
    MQTTStatus_t status = MQTTIllegalState;
    bool shouldDeleteRecord = false;
    bool isTransitionValid = false;

    assert( records != NULL );

    /* Record to be deleted if the state transition is completed or if a PUBREC
     * is received for an outgoing QoS2 publish. When a PUBREC is received,
     * record is deleted and added back to the end of the records to maintain
     * ordering for PUBRELs. */
    shouldDeleteRecord = ( newState == MQTTPublishDone ) || ( newState == MQTTPubRelSend );
    isTransitionValid = validateTransitionAck( currentState, newState );

    if( isTransitionValid == true )
    {
        status = MQTTSuccess;

        /* Update record for acks. When sending or receiving acks for packets that
         * are resent during a session reestablishment, the new state and
         * current state can be the same. No update of record required in that case. */
        if( currentState != newState )
        {
            updateRecord( records,
                          recordIndex,
                          newState,
                          shouldDeleteRecord );

            /* For QoS2 messages, in order to preserve the message ordering, when
             * a PUBREC is received for an outgoing publish, the record should be
             * moved to the last. This move will help preserve the order in which
             * a PUBREL needs to be resent in case of a session reestablishment. */
            if( newState == MQTTPubRelSend )
            {
                status = addRecord( records,
                                    maxRecordCount,
                                    packetId,
                                    MQTTQoS2,
                                    MQTTPubRelSend );
            }
        }
    }
    else
    {
        /* Invalid state transition. */
        LogError( ( "Invalid transition from state %s to state %s.",
                    MQTT_State_strerror( currentState ),
                    MQTT_State_strerror( newState ) ) );
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t updateStatePublish( const MQTTContext_t * pMqttContext,
                                        size_t recordIndex,
                                        uint16_t packetId,
                                        MQTTStateOperation_t opType,
                                        MQTTQoS_t qos,
                                        MQTTPublishState_t currentState,
                                        MQTTPublishState_t newState )
{
    MQTTStatus_t status = MQTTSuccess;
    bool isTransitionValid = false;

    assert( pMqttContext != NULL );
    assert( packetId != MQTT_PACKET_ID_INVALID );
    assert( qos != MQTTQoS0 );

    /* This will always succeed for an incoming publish. This is due to the fact
     * that the passed in currentState must be MQTTStateNull, since
     * #MQTT_UpdateStatePublish does not perform a lookup for receives. */
    isTransitionValid = validateTransitionPublish( currentState, newState, opType, qos );

    if( isTransitionValid == true )
    {
        /* addRecord will check for collisions. */
        if( opType == MQTT_RECEIVE )
        {
            status = addRecord( pMqttContext->incomingPublishRecords,
                                pMqttContext->incomingPublishRecordMaxCount,
                                packetId,
                                qos,
                                newState );
        }
        /* Send operation. */
        else
        {
            /* Skip updating record when publish is resend and no state
             * update is required. */
            if( currentState != newState )
            {
                updateRecord( pMqttContext->outgoingPublishRecords,
                              recordIndex,
                              newState,
                              false );
            }
        }
    }
    else
    {
        status = MQTTIllegalState;
        LogError( ( "Invalid transition from state %s to state %s.",
                    MQTT_State_strerror( currentState ),
                    MQTT_State_strerror( newState ) ) );
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_ReserveState( const MQTTContext_t * pMqttContext,
                                uint16_t packetId,
                                MQTTQoS_t qos )
{
    MQTTStatus_t status = MQTTSuccess;

    if( qos == MQTTQoS0 )
    {
        status = MQTTSuccess;
    }
    else if( ( packetId == MQTT_PACKET_ID_INVALID ) || ( pMqttContext == NULL ) )
    {
        status = MQTTBadParameter;
    }
    else
    {
        /* Collisions are detected when adding the record. */
        status = addRecord( pMqttContext->outgoingPublishRecords,
                            pMqttContext->outgoingPublishRecordMaxCount,
                            packetId,
                            qos,
                            MQTTPublishSend );
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTPublishState_t MQTT_CalculateStatePublish( MQTTStateOperation_t opType,
                                               MQTTQoS_t qos )
{
    MQTTPublishState_t calculatedState = MQTTStateNull;

    switch( qos )
    {
        case MQTTQoS0:
            calculatedState = MQTTPublishDone;
            break;

        case MQTTQoS1:
            calculatedState = ( opType == MQTT_SEND ) ? MQTTPubAckPending : MQTTPubAckSend;
            break;

        case MQTTQoS2:
            calculatedState = ( opType == MQTT_SEND ) ? MQTTPubRecPending : MQTTPubRecSend;
            break;

        default:
            /* No other QoS values. */
            break;
    }

    return calculatedState;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_UpdateStatePublish( const MQTTContext_t * pMqttContext,
                                      uint16_t packetId,
                                      MQTTStateOperation_t opType,
                                      MQTTQoS_t qos,
                                      MQTTPublishState_t * pNewState )
{
    MQTTPublishState_t newState = MQTTStateNull;
    MQTTPublishState_t currentState = MQTTStateNull;
    MQTTStatus_t mqttStatus = MQTTSuccess;
    size_t recordIndex = MQTT_INVALID_STATE_COUNT;
    MQTTQoS_t foundQoS = MQTTQoS0;

    if( ( pMqttContext == NULL ) || ( pNewState == NULL ) )
    {
        LogError( ( "Argument cannot be NULL: pMqttContext=%p, pNewState=%p",
                    ( const void * ) pMqttContext,
                    ( void * ) pNewState ) );

        mqttStatus = MQTTBadParameter;
    }
    else if( qos == MQTTQoS0 )
    {
        /* QoS 0 publish. Do nothing. */
        *pNewState = MQTTPublishDone;
    }
    else if( packetId == MQTT_PACKET_ID_INVALID )
    {
        /* Publishes > QoS 0 need a valid packet ID. */
        mqttStatus = MQTTBadParameter;
    }
    else if( opType == MQTT_SEND )
    {
        /* Search record for entry so we can check QoS. */
        recordIndex = findInRecord( pMqttContext->outgoingPublishRecords,
                                    pMqttContext->outgoingPublishRecordMaxCount,
                                    packetId,
                                    &foundQoS,
                                    &currentState );

        if( ( recordIndex == MQTT_INVALID_STATE_COUNT ) || ( foundQoS != qos ) )
        {
            /* Entry should match with supplied QoS. */
            mqttStatus = MQTTBadParameter;
        }
    }
    else
    {
        /* QoS 1 or 2 receive. Nothing to be done. */
    }

    if( ( qos != MQTTQoS0 ) && ( mqttStatus == MQTTSuccess ) )
    {
        newState = MQTT_CalculateStatePublish( opType, qos );
        /* Validate state transition and update state records. */
        mqttStatus = updateStatePublish( pMqttContext,
                                         recordIndex,
                                         packetId,
                                         opType,
                                         qos,
                                         currentState,
                                         newState );

        /* Update output parameter on success. */
        if( mqttStatus == MQTTSuccess )
        {
            *pNewState = newState;
        }
    }

    return mqttStatus;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_RemoveStateRecord( const MQTTContext_t * pMqttContext,
                                     uint16_t packetId )
{
    MQTTStatus_t status = MQTTSuccess;
    MQTTPubAckInfo_t * records;
    size_t recordIndex;
    /* Current state is updated by the findInRecord function. */
    MQTTPublishState_t currentState;
    MQTTQoS_t qos = MQTTQoS0;


    if( ( pMqttContext == NULL ) || ( ( pMqttContext->outgoingPublishRecords == NULL ) ) )
    {
        status = MQTTBadParameter;
    }
    else
    {
        records = pMqttContext->outgoingPublishRecords;

        recordIndex = findInRecord( records,
                                    pMqttContext->outgoingPublishRecordMaxCount,
                                    packetId,
                                    &qos,
                                    &currentState );

        if( currentState == MQTTStateNull )
        {
            status = MQTTBadParameter;
        }
        else if( ( qos != MQTTQoS1 ) && ( qos != MQTTQoS2 ) )
        {
            status = MQTTBadParameter;
        }
        else
        {
            /* Delete the record. */
            updateRecord( records,
                          recordIndex,
                          MQTTStateNull,
                          true );
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_UpdateStateAck( const MQTTContext_t * pMqttContext,
                                  uint16_t packetId,
                                  MQTTPubAckType_t packetType,
                                  MQTTStateOperation_t opType,
                                  MQTTPublishState_t * pNewState )
{
    MQTTPublishState_t newState = MQTTStateNull;
    MQTTPublishState_t currentState = MQTTStateNull;
    bool isOutgoingPublish = isPublishOutgoing( packetType, opType );
    MQTTQoS_t qos = MQTTQoS0;
    size_t maxRecordCount = MQTT_INVALID_STATE_COUNT;
    size_t recordIndex = MQTT_INVALID_STATE_COUNT;

    MQTTPubAckInfo_t * records = NULL;
    MQTTStatus_t status = MQTTBadResponse;

    if( ( pMqttContext == NULL ) || ( pNewState == NULL ) )
    {
        LogError( ( "Argument cannot be NULL: pMqttContext=%p, pNewState=%p.",
                    ( const void * ) pMqttContext,
                    ( void * ) pNewState ) );
        status = MQTTBadParameter;
    }
    else if( packetId == MQTT_PACKET_ID_INVALID )
    {
        LogError( ( "Packet ID must be nonzero." ) );
        status = MQTTBadParameter;
    }
    else if( packetType > MQTTPubcomp )
    {
        LogError( ( "Invalid packet type %u.", ( unsigned int ) packetType ) );
        status = MQTTBadParameter;
    }
    else
    {
        if( isOutgoingPublish == true )
        {
            records = pMqttContext->outgoingPublishRecords;
            maxRecordCount = pMqttContext->outgoingPublishRecordMaxCount;
        }
        else
        {
            records = pMqttContext->incomingPublishRecords;
            maxRecordCount = pMqttContext->incomingPublishRecordMaxCount;
        }

        recordIndex = findInRecord( records,
                                    maxRecordCount,
                                    packetId,
                                    &qos,
                                    &currentState );
    }

    if( recordIndex != MQTT_INVALID_STATE_COUNT )
    {
        newState = MQTT_CalculateStateAck( packetType, opType, qos );

        /* Validate state transition and update state record. */
        status = updateStateAck( records,
                                 maxRecordCount,
                                 recordIndex,
                                 packetId,
                                 currentState,
                                 newState );

        /* Update the output parameter. */
        if( status == MQTTSuccess )
        {
            *pNewState = newState;
        }
    }
    else
    {
        LogError( ( "No matching record found for publish: PacketId=%u.",
                    ( unsigned int ) packetId ) );
    }

    return status;
}

/*-----------------------------------------------------------*/

uint16_t MQTT_PubrelToResend( const MQTTContext_t * pMqttContext,
                              MQTTStateCursor_t * pCursor,
                              MQTTPublishState_t * pState )
{
    uint16_t packetId = MQTT_PACKET_ID_INVALID;
    uint16_t searchStates = 0U;

    /* Validate arguments. */
    if( ( pMqttContext == NULL ) || ( pCursor == NULL ) || ( pState == NULL ) )
    {
        LogError( ( "Arguments cannot be NULL pMqttContext=%p, pCursor=%p"
                    " pState=%p.",
                    ( const void * ) pMqttContext,
                    ( void * ) pCursor,
                    ( void * ) pState ) );
    }
    else
    {
        /* PUBREL for packets in state #MQTTPubCompPending and #MQTTPubRelSend
         * would need to be resent when a session is reestablished. */
        UINT16_SET_BIT( searchStates, MQTTPubCompPending );
        UINT16_SET_BIT( searchStates, MQTTPubRelSend );
        packetId = stateSelect( pMqttContext, searchStates, pCursor );

        /* The state needs to be in #MQTTPubRelSend for sending PUBREL. */
        if( packetId != MQTT_PACKET_ID_INVALID )
        {
            *pState = MQTTPubRelSend;
        }
    }

    return packetId;
}

/*-----------------------------------------------------------*/

uint16_t MQTT_PublishToResend( const MQTTContext_t * pMqttContext,
                               MQTTStateCursor_t * pCursor )
{
    uint16_t packetId = MQTT_PACKET_ID_INVALID;
    uint16_t searchStates = 0U;

    /* Validate arguments. */
    if( ( pMqttContext == NULL ) || ( pCursor == NULL ) )
    {
        LogError( ( "Arguments cannot be NULL pMqttContext=%p, pCursor=%p",
                    ( const void * ) pMqttContext,
                    ( void * ) pCursor ) );
    }
    else
    {
        /* Packets in state #MQTTPublishSend, #MQTTPubAckPending and
         * #MQTTPubRecPending would need to be resent when a session is
         * reestablished. */
        UINT16_SET_BIT( searchStates, MQTTPublishSend );
        UINT16_SET_BIT( searchStates, MQTTPubAckPending );
        UINT16_SET_BIT( searchStates, MQTTPubRecPending );

        packetId = stateSelect( pMqttContext, searchStates, pCursor );
    }

    return packetId;
}

/*-----------------------------------------------------------*/

const char * MQTT_State_strerror( MQTTPublishState_t state )
{
    const char * str = NULL;

    switch( state )
    {
        case MQTTStateNull:
            str = "MQTTStateNull";
            break;

        case MQTTPublishSend:
            str = "MQTTPublishSend";
            break;

        case MQTTPubAckSend:
            str = "MQTTPubAckSend";
            break;

        case MQTTPubRecSend:
            str = "MQTTPubRecSend";
            break;

        case MQTTPubRelSend:
            str = "MQTTPubRelSend";
            break;

        case MQTTPubCompSend:
            str = "MQTTPubCompSend";
            break;

        case MQTTPubAckPending:
            str = "MQTTPubAckPending";
            break;

        case MQTTPubRecPending:
            str = "MQTTPubRecPending";
            break;

        case MQTTPubRelPending:
            str = "MQTTPubRelPending";
            break;

        case MQTTPubCompPending:
            str = "MQTTPubCompPending";
            break;

        case MQTTPublishDone:
            str = "MQTTPublishDone";
            break;

        default:
            /* Invalid state received. */
            str = "Invalid MQTT State";
            break;
    }

    return str;
}

/*-----------------------------------------------------------*/

// === source/core_mqtt.c (verbatim from upstream) ===
/*
 * coreMQTT
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

/**
 * @file core_mqtt.c
 * @brief Implements the user-facing functions in core_mqtt.h.
 */
#include <string.h>
#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <inttypes.h>
#include <stddef.h>




/* Include config defaults header to get default values of configs. */

#ifndef MQTT_PRE_STATE_UPDATE_HOOK

/**
 * @brief Hook called just before an update to the MQTT state is made.
 */
    #define MQTT_PRE_STATE_UPDATE_HOOK( pContext )
#endif /* !MQTT_PRE_STATE_UPDATE_HOOK */

#ifndef MQTT_POST_STATE_UPDATE_HOOK

/**
 * @brief Hook called just after an update to the MQTT state has
 * been made.
 */
    #define MQTT_POST_STATE_UPDATE_HOOK( pContext )
#endif /* !MQTT_POST_STATE_UPDATE_HOOK */

/**
 * @brief Bytes required to encode any string length in an MQTT packet header.
 * Length is always encoded in two bytes according to the MQTT specification.
 */
#define CORE_MQTT_SERIALIZED_LENGTH_FIELD_BYTES          ( 2U )

/**
 * @brief Number of vectors required to encode one topic filter in a subscribe
 * request. Three vectors are required as there are three fields in the
 * subscribe request namely:
 * 1. Topic filter length; 2. Topic filter; and 3. Subscription options in this order.
 */
#define CORE_MQTT_SUBSCRIBE_PER_TOPIC_VECTOR_LENGTH      ( 3U )

/**
 * @brief Number of vectors required to encode one topic filter in an
 * unsubscribe request. Two vectors are required as there are two fields in the
 * unsubscribe request namely:
 * 1. Topic filter length; and 2. Topic filter in this order.
 */
#define CORE_MQTT_UNSUBSCRIBE_PER_TOPIC_VECTOR_LENGTH    ( 2U )

/**
 * @brief Set flag in the packet ID just beyond the actual packet ID.
 */
#define SET_INCOMING_PUB_FLAG( packetID )    ( ( uint32_t ) ( ( ( uint32_t ) packetID ) | ( ( ( uint32_t ) 1U ) << 16U ) ) )

struct MQTTVec
{
    TransportOutVector_t * pVector; /**< Pointer to transport vector. USER SHOULD NOT ACCESS THIS DIRECTLY - IT IS AN INTERNAL DETAIL AND CAN CHANGE. */
    size_t vectorLen;               /**< Length of the transport vector. USER SHOULD NOT ACCESS THIS DIRECTLY - IT IS AN INTERNAL DETAIL AND CAN CHANGE. */
};

/*-----------------------------------------------------------*/

/**
 * @brief Sends provided buffer to network using transport send.
 *
 * @brief param[in] pContext Initialized MQTT context.
 * @brief param[in] pBufferToSend Buffer to be sent to network.
 * @brief param[in] bytesToSend Number of bytes to be sent.
 *
 * @note This operation may call the transport send function
 * repeatedly to send bytes over the network until either:
 * 1. The requested number of bytes @a bytesToSend have been sent.
 *                    OR
 * 2. MQTT_SEND_TIMEOUT_MS milliseconds have gone by since entering this
 * function.
 *                    OR
 * 3. There is an error in sending data over the network.
 *
 * @return Total number of bytes sent, or negative value on network error.
 */
static int32_t sendBuffer( MQTTContext_t * pContext,
                           const uint8_t * pBufferToSend,
                           size_t bytesToSend );

/**
 * @brief Sends MQTT connect without copying the users data into any buffer.
 *
 * @param[in] pContext Initialized MQTT context.
 * @param[in] pConnectInfo MQTT CONNECT packet information.
 * @param[in] pWillInfo Last Will and Testament. Pass NULL if Last Will and
 * Testament is not used.
 * @param[in] remainingLength the length of the connect packet.
 * @param[in] pPropertyBuilder Property builder containing CONNECT properties.
 * @param[in] pWillPropertyBuilder Property builder containing Last Will And Testament properties.
 * @note This operation may call the transport send function
 * repeatedly to send bytes over the network until either:
 * 1. The requested number of bytes @a remainingLength have been sent.
 *                    OR
 * 2. MQTT_SEND_TIMEOUT_MS milliseconds have gone by since entering this
 * function.
 *                    OR
 * 3. There is an error in sending data over the network.
 *
 * @return #MQTTSendFailed, #MQTTBadParameter, #MQTTBadResponse or #MQTTSuccess.
 */
static MQTTStatus_t sendConnectWithoutCopy( MQTTContext_t * pContext,
                                            const MQTTConnectInfo_t * pConnectInfo,
                                            const MQTTPublishInfo_t * pWillInfo,
                                            uint32_t remainingLength,
                                            const MQTTPropBuilder_t * pPropertyBuilder,
                                            const MQTTPropBuilder_t * pWillPropertyBuilder );

/**
 * @brief Sends the vector array passed through the parameters over the network.
 *
 * @note The preference is given to 'writev' function if it is present in the
 * transport interface. Otherwise, a send call is made repeatedly to achieve the
 * result.
 *
 * @param[in] pContext Initialized MQTT context.
 * @param[in] pIoVec The vector array to be sent.
 * @param[in] ioVecCount The number of elements in the array.
 *
 * @note This operation may call the transport send or writev functions
 * repeatedly to send bytes over the network until either:
 * 1. The requested number of bytes have been sent.
 *                    OR
 * 2. MQTT_SEND_TIMEOUT_MS milliseconds have gone by since entering this
 * function.
 *                    OR
 * 3. There is an error in sending data over the network.
 *
 * @return The total number of bytes sent or the error code as received from the
 * transport interface.
 */
static int32_t sendMessageVector( MQTTContext_t * pContext,
                                  TransportOutVector_t * pIoVec,
                                  size_t ioVecCount );

/**
 * @brief Add a string and its length after serializing it in a manner outlined by
 * the MQTT specification.
 *
 * @param[in] serializedLength Array of two bytes to which the vector will point.
 * The array must remain in scope until the message has been sent.
 * @param[in] string The string to be serialized.
 * @param[in] length The length of the string to be serialized.
 * @param[in] iterator The iterator pointing to the first element in the
 * transport interface IO array.
 * @param[out] updatedLength This parameter will be added to with the number of
 * bytes added to the vector.
 *
 * @return The number of vectors added.
 */
static size_t addEncodedStringToVector( uint8_t serializedLength[ CORE_MQTT_SERIALIZED_LENGTH_FIELD_BYTES ],
                                        const char * const string,
                                        uint16_t length,
                                        TransportOutVector_t * iterator,
                                        uint32_t * updatedLength );

/**
 * @brief Send Subscribe without copying the users data into any buffer.
 *
 * @param[in] pContext Initialized MQTT context.
 * @param[in] pSubscriptionList List of MQTT subscription info.
 * @param[in] subscriptionCount Number of elements in pSubscriptionList.
 * @param[in] packetId Packet identifier.
 * @param[in] remainingLength Remaining length of the packet.
 * @param[in] pPropertyBuilder MQTT property builder.
 * @note This operation may call the transport send function
 * repeatedly to send bytes over the network until either:
 * 1. The requested number of bytes @a remainingLength have been sent.
 *                    OR
 * 2. MQTT_SEND_TIMEOUT_MS milliseconds have gone by since entering this
 * function.
 *                    OR
 * 3. There is an error in sending data over the network.
 *
 * @return #MQTTSendFailed or #MQTTSuccess.
 */

static MQTTStatus_t sendSubscribeWithoutCopy( MQTTContext_t * pContext,
                                              const MQTTSubscribeInfo_t * pSubscriptionList,
                                              size_t subscriptionCount,
                                              uint16_t packetId,
                                              uint32_t remainingLength,
                                              const MQTTPropBuilder_t * pPropertyBuilder );

/**
 * @brief Send Unsubscribe without copying the users data into any buffer.
 *
 * @param[in] pContext Initialized MQTT context.
 * @param[in] pSubscriptionList List of MQTT subscription info.
 * @param[in] subscriptionCount Number of elements in pSubscriptionList.
 * @param[in] packetId Packet identifier.
 * @param[in] remainingLength Remaining length of the packet.
 * @param[in] pPropertyBuilder MQTT property builder.
 * @note This operation may call the transport send function
 * repeatedly to send bytes over the network until either:
 * 1. The requested number of bytes @a remainingLength have been sent.
 *                    OR
 * 2. MQTT_SEND_TIMEOUT_MS milliseconds have gone by since entering this
 * function.
 *                    OR
 * 3. There is an error in sending data over the network.
 *
 * @return #MQTTSendFailed or #MQTTSuccess.
 */
static MQTTStatus_t sendUnsubscribeWithoutCopy( MQTTContext_t * pContext,
                                                const MQTTSubscribeInfo_t * pSubscriptionList,
                                                size_t subscriptionCount,
                                                uint16_t packetId,
                                                uint32_t remainingLength,
                                                const MQTTPropBuilder_t * pPropertyBuilder );

/**
 * @brief Calculate the interval between two millisecond timestamps, including
 * when the later value has overflowed.
 *
 * @note In C, the operands are promoted to signed integers in subtraction.
 * Using this function avoids the need to cast the result of subtractions back
 * to uint32_t.
 *
 * @param[in] later The later time stamp, in milliseconds.
 * @param[in] start The earlier time stamp, in milliseconds.
 *
 * @return later - start.
 */
static uint32_t calculateElapsedTime( uint32_t later,
                                      uint32_t start );

/**
 * @brief Convert a byte indicating a publish ack type to an #MQTTPubAckType_t.
 *
 * @param[in] packetType First byte of fixed header.
 *
 * @return Type of ack.
 */
static MQTTPubAckType_t getAckFromPacketType( uint8_t packetType );

/**
 * @brief Receive bytes into the network buffer.
 *
 * @param[in] pContext Initialized MQTT Context.
 * @param[in] bytesToRecv Number of bytes to receive.
 *
 * @note This operation calls the transport receive function
 * repeatedly to read bytes from the network until either:
 * 1. The requested number of bytes @a bytesToRecv are read.
 *                    OR
 * 2. No data is received from the network for MQTT_RECV_POLLING_TIMEOUT_MS duration.
 *
 *                    OR
 * 3. There is an error in reading from the network.
 *
 *
 * @return Number of bytes received, or negative number on network error.
 */
static int32_t recvExact( MQTTContext_t * pContext,
                          size_t bytesToRecv );

/**
 * @brief Receive a CONNACK packet from the transport interface.
 *
 * @param[in] pContext MQTT Connection context.
 * @param[in] incomingPacket packet struct with remaining length.
 *
 * @return #MQTTSuccess or #MQTTRecvFailed.
 */
static MQTTStatus_t receiveConnackPacket( MQTTContext_t * pContext,
                                          MQTTPacketInfo_t incomingPacket );

/**
 * @brief Get the correct ack type to send.
 *
 * @param[in] state Current state of publish.
 *
 * @return Packet Type byte of PUBACK, PUBREC, PUBREL, or PUBCOMP if one of
 * those should be sent, else 0.
 */
static uint8_t getAckTypeToSend( MQTTPublishState_t state );

/**
 * @brief Send acks for received QoS 1/2 publishes.
 *
 * @param[in] pContext MQTT Connection context.
 * @param[in] packetId packet ID of original PUBLISH.
 * @param[in] publishState Current publish state in record.
 *
 * @return #MQTTSuccess, #MQTTIllegalState or #MQTTSendFailed.
 */
static MQTTStatus_t sendPublishAcks( MQTTContext_t * pContext,
                                     uint16_t packetId,
                                     MQTTPublishState_t publishState );

/**
 * @brief Send a keep alive PINGREQ if the keep alive interval has elapsed.
 *
 * @param[in] pContext Initialized MQTT Context.
 *
 * @return #MQTTKeepAliveTimeout if a PINGRESP is not received in time,
 * #MQTTSendFailed if the PINGREQ cannot be sent, or #MQTTSuccess.
 */
static MQTTStatus_t handleKeepAlive( MQTTContext_t * pContext );

/**
 * @brief Handle received MQTT PUBLISH packet.
 *
 * @param[in] pContext MQTT Connection context.
 * @param[in] pIncomingPacket Incoming packet.
 *
 * @return MQTTSuccess, MQTTIllegalState or deserialization error.
 */
static MQTTStatus_t handleIncomingPublish( MQTTContext_t * pContext,
                                           MQTTPacketInfo_t * pIncomingPacket );

/**
 * @brief Handle received MQTT publish acks.
 *
 * @param[in] pContext MQTT Connection context.
 * @param[in] pIncomingPacket Incoming packet.
 *
 * @return MQTTSuccess, MQTTIllegalState, or deserialization error.
 */
static MQTTStatus_t handlePublishAcks( MQTTContext_t * pContext,
                                       MQTTPacketInfo_t * pIncomingPacket );

/**
 * @brief Handle received MQTT ack.
 *
 * @param[in] pContext MQTT Connection context.
 * @param[in] pIncomingPacket Incoming packet.
 * @param[in] manageKeepAlive Flag indicating if PINGRESPs should not be given
 * to the application
 *
 * @return MQTTSuccess, MQTTIllegalState, or deserialization error.
 */
static MQTTStatus_t handleIncomingAck( MQTTContext_t * pContext,
                                       MQTTPacketInfo_t * pIncomingPacket,
                                       bool manageKeepAlive );

/**
 * @brief Run a single iteration of the receive loop.
 *
 * @param[in] pContext MQTT Connection context.
 * @param[in] manageKeepAlive Flag indicating if keep alive should be handled.
 *
 * @return #MQTTRecvFailed if a network error occurs during reception;
 * #MQTTSendFailed if a network error occurs while sending an ACK or PINGREQ;
 * #MQTTBadResponse if an invalid packet is received;
 * #MQTTKeepAliveTimeout if the server has not sent a PINGRESP before
 * #MQTT_PINGRESP_TIMEOUT_MS milliseconds;
 * #MQTTIllegalState if an incoming QoS 1/2 publish or ack causes an
 * invalid transition for the internal state machine;
 * #MQTTSuccess on success.
 */
static MQTTStatus_t receiveSingleIteration( MQTTContext_t * pContext,
                                            bool manageKeepAlive );

/**
 * @brief Validates parameters of #MQTT_Subscribe or #MQTT_Unsubscribe.
 *
 * @param[in] pContext Initialized MQTT context.
 * @param[in] pSubscriptionList List of MQTT subscription info.
 * @param[in] subscriptionCount The number of elements in pSubscriptionList.
 * @param[in] packetId Packet identifier.
 * @param[in] subscriptionType Either #MQTT_TYPE_SUBSCRIBE or #MQTT_TYPE_UNSUBSCRIBE.
 *
 * @return #MQTTBadParameter if invalid parameters are passed;
 * #MQTTSuccess otherwise.
 */
static MQTTStatus_t validateSubscribeUnsubscribeParams( const MQTTContext_t * pContext,
                                                        const MQTTSubscribeInfo_t * pSubscriptionList,
                                                        size_t subscriptionCount,
                                                        uint16_t packetId,
                                                        MQTTSubscriptionType_t subscriptionType );

/**
 * @brief Receives a CONNACK MQTT packet.
 *
 * @param[in] pContext Initialized MQTT context.
 * @param[in] timeoutMs Timeout for waiting for CONNACK packet.
 * @param[in] cleanSession Clean session flag set by application.
 * @param[out] pIncomingPacket List of MQTT subscription info.
 * @param[out] pSessionPresent Whether a previous session was present.
 * Only relevant if not establishing a clean session.
 *
 * @return #MQTTBadResponse if a bad response is received;
 * #MQTTNoDataAvailable if no data available for transport recv;
 * ##MQTTRecvFailed if transport recv failed;
 * #MQTTSuccess otherwise.
 */
static MQTTStatus_t receiveConnack( MQTTContext_t * pContext,
                                    uint32_t timeoutMs,
                                    bool cleanSession,
                                    MQTTPacketInfo_t * pIncomingPacket,
                                    bool * pSessionPresent );

/**
 * @brief Resends pending acks for a re-established MQTT session
 *
 * @param[in] pContext Initialized MQTT context.
 *
 * @return #MQTTSendFailed if transport send during resend failed;
 * #MQTTSuccess otherwise.
 */
static MQTTStatus_t handleUncleanSessionResumption( MQTTContext_t * pContext );

/**
 * @brief Clears existing state records for a clean session.
 *
 * @param[in] pContext Initialized MQTT context.
 *
 * @return #MQTTSuccess always otherwise.
 */
static MQTTStatus_t handleCleanSession( MQTTContext_t * pContext );

/**
 * @brief Send the publish packet without copying the topic string and payload in
 * the buffer.
 *
 * @param[in] pContext Initialized MQTT context.
 * @param[in] pPublishInfo MQTT PUBLISH packet parameters.
 * @param[in] pMqttHeader the serialized MQTT header with the header byte;
 * the encoded length of the packet; and the encoded length of the topic string.
 * @param[in] headerSize Size of the serialized PUBLISH header.
 * @param[in] packetId Packet Id of the publish packet.
 * @param[in] pPropertyBuilder MQTT Publish property builder.
 *
 * @return #MQTTSendFailed if transport send during resend failed;
 * #MQTTPublishStoreFailed if storing the outgoing publish failed in the case of QoS 1/2
 * #MQTTSuccess otherwise.
 */
static MQTTStatus_t sendPublishWithoutCopy( MQTTContext_t * pContext,
                                            const MQTTPublishInfo_t * pPublishInfo,
                                            uint8_t * pMqttHeader,
                                            size_t headerSize,
                                            uint16_t packetId,
                                            const MQTTPropBuilder_t * pPropertyBuilder );

/**
 * @brief Function to validate #MQTT_Publish parameters.
 *
 * @param[in] pContext Initialized MQTT context.
 * @param[in] pPublishInfo MQTT PUBLISH packet parameters.
 * @param[in] packetId Packet Id for the MQTT PUBLISH packet.
 *
 * @return #MQTTBadParameter if invalid parameters are passed;
 * #MQTTSuccess otherwise.
 */
static MQTTStatus_t validatePublishParams( const MQTTContext_t * pContext,
                                           const MQTTPublishInfo_t * pPublishInfo,
                                           uint16_t packetId );

/**
 * @brief Performs matching for special cases when a topic filter ends
 * with a wildcard character.
 *
 * When the topic name has been consumed but there are remaining characters to
 * to match in topic filter, this function handles the following 2 cases:
 * - When the topic filter ends with "/+" or "/#" characters, but the topic
 * name only ends with '/'.
 * - When the topic filter ends with "/#" characters, but the topic name
 * ends at the parent level.
 *
 * @note This function ASSUMES that the topic name been consumed in linear
 * matching with the topic filer, but the topic filter has remaining characters
 * to be matched.
 *
 * @param[in] pTopicFilter The topic filter containing the wildcard.
 * @param[in] topicFilterLength Length of the topic filter being examined.
 * @param[in] filterIndex Index of the topic filter being examined.
 *
 * @return Returns whether the topic filter and the topic name match.
 */
static bool matchEndWildcardsSpecialCases( const char * pTopicFilter,
                                           uint16_t topicFilterLength,
                                           uint16_t filterIndex );

/**
 * @brief Attempt to match topic name with a topic filter starting with a wildcard.
 *
 * If the topic filter starts with a '+' (single-level) wildcard, the function
 * advances the @a pNameIndex by a level in the topic name.
 * If the topic filter starts with a '#' (multi-level) wildcard, the function
 * concludes that both the topic name and topic filter match.
 *
 * @param[in] pTopicName The topic name to match.
 * @param[in] topicNameLength Length of the topic name.
 * @param[in] pTopicFilter The topic filter to match.
 * @param[in] topicFilterLength Length of the topic filter.
 * @param[in,out] pNameIndex Current index in the topic name being examined. It is
 * advanced by one level for `+` wildcards.
 * @param[in, out] pFilterIndex Current index in the topic filter being examined.
 * It is advanced to position of '/' level separator for '+' wildcard.
 * @param[out] pMatch Whether the topic filter and topic name match.
 *
 * @return `true` if the caller of this function should exit; `false` if the
 * caller should continue parsing the topics.
 */
static bool matchWildcards( const char * pTopicName,
                            uint16_t topicNameLength,
                            const char * pTopicFilter,
                            uint16_t topicFilterLength,
                            uint16_t * pNameIndex,
                            uint16_t * pFilterIndex,
                            bool * pMatch );

/**
 * @brief Match a topic name and topic filter allowing the use of wildcards.
 *
 * @param[in] pTopicName The topic name to check.
 * @param[in] topicNameLength Length of the topic name.
 * @param[in] pTopicFilter The topic filter to check.
 * @param[in] topicFilterLength Length of topic filter.
 *
 * @return `true` if the topic name and topic filter match; `false` otherwise.
 */
static bool matchTopicFilter( const char * pTopicName,
                              uint16_t topicNameLength,
                              const char * pTopicFilter,
                              uint16_t topicFilterLength );

/**
 * @brief Validate the topic filter in a subscription.
 *
 * @param[in] pContext MQTT Connection context.
 * @param[in] pSubscriptionList List of MQTT subscription info.
 * @param[in] iterator The iterator pointing to a topic filter in pSubscriptionList.
 * @param[in] subscriptionType The type of subscription, either #MQTT_TYPE_SUBSCRIBE or #MQTT_TYPE_UNSUBSCRIBE.
 *
 * @return Returns one of the following:
 * - #MQTTSuccess if the topic filter is valid
 * - #MQTTBadParameter if the topic filter is invalid or parameters are NULL
 */
static MQTTStatus_t validateTopicFilter( const MQTTContext_t * pContext,
                                         const MQTTSubscribeInfo_t * pSubscriptionList,
                                         size_t iterator,
                                         MQTTSubscriptionType_t subscriptionType );

/**
 * @brief Check if wildcard subscriptions are allowed and valid.
 *
 * @param[in] isWildcardAvailable Flag indicating if wildcard subscriptions are supported.
 * @param[in] pSubscriptionList List of MQTT subscription info.
 * @param[in] iterator The iterator pointing to a topic filter in pSubscriptionList.
 *
 * @return true if wildcard subscriptions are valid or not present;
 *         false if wildcards are used but not supported
 */
static bool checkWildcardSubscriptions( uint8_t isWildcardAvailable,
                                        const MQTTSubscribeInfo_t * pSubscriptionList,
                                        size_t iterator );

/**
 * @brief Validate Shared Subscriptions
 *
 * @param[in] pContext MQTT Connection context.
 * @param[in] pSubscriptionList List of MQTT subscription info.
 * @param[in] iterator The iterator pointing to a topic filter in pSubscriptionList.
 *
 * @return #MQTTBadParameter if invalid parameters are passed;
 *         #MQTTSuccess otherwise
 * */
static MQTTStatus_t validateSharedSubscriptions( const MQTTContext_t * pContext,
                                                 const MQTTSubscribeInfo_t * pSubscriptionList,
                                                 const size_t iterator );

/**
 * @brief Add subscription options to the options array.
 *
 * @param[in] subscriptionInfo MQTT subscription information.
 * @param[out] pSubscriptionOptionsArray Array to store subscription options.
 * @param[in] currentOptionIndex Current index in the options array.
 *
 * @note This function does not return a status as it performs a direct array update.
 */
static void addSubscriptionOptions( const MQTTSubscribeInfo_t subscriptionInfo,
                                    uint8_t * pSubscriptionOptionsArray,
                                    size_t currentOptionIndex );

/**
 * @brief Handle incoming SUBACK or UNSUBACK packet.
 *
 * Deserializes the packet and invokes the application callback. Server
 * rejection of individual topic filters (reason codes >= 0x80) is not
 * treated as a library-level error; the application can inspect per-topic
 * reason codes via #MQTTDeserializedInfo_t.pReasonCode in the callback.
 *
 * @param[in] pContext MQTT Connection context.
 * @param[in] pIncomingPacket Information of incoming packet.
 *
 * @return #MQTTSuccess on successful deserialization (including server refusal);
 * #MQTTBadResponse if the packet is malformed;
 * #MQTTBadParameter if parameters are invalid;
 * #MQTTEventCallbackFailed if the application callback returns false.
 */
static MQTTStatus_t handleSubUnsubAck( MQTTContext_t * pContext,
                                       MQTTPacketInfo_t * pIncomingPacket );

/**
 * @brief Send acks for received QoS 1/2 publishes. This function is used to send
 *        Publish Acks without any properties or reason codes.
 *
 * @param[in] pContext MQTT Connection context.
 * @param[in] packetId packet ID of original PUBLISH.
 * @param[in] publishState Current publish state in record.
 *
 * @return MQTTSuccess, MQTTBadParameter, MQTTBadResponse, MQTTIllegalState, MQTTSendFailed, MQTTStatusNotConnected, MQTTStatusDisconnectPending or MQTTNoMemory.
 */
static MQTTStatus_t sendPublishAcksWithoutProperty( MQTTContext_t * pContext,
                                                    uint16_t packetId,
                                                    MQTTPublishState_t publishState );

/**
 * @brief Send acks for received QoS 1/2 publishes with properties.
 *
 * @param[in] pContext MQTT Connection context.
 * @param[in] packetId packet ID of original PUBLISH.
 * @param[in] publishState Current publish state in record.
 * @param[in] reasonCode Reason code to be sent in the Publish Ack.
 *
 * @return #MQTTSuccess, #MQTTBadParameter, #MQTTIllegalState, #MQTTSendFailed, #MQTTStatusNotConnected, #MQTTStatusDisconnectPending or #MQTTBadResponse.
 */
static MQTTStatus_t sendPublishAcksWithProperty( MQTTContext_t * pContext,
                                                 uint16_t packetId,
                                                 MQTTPublishState_t publishState,
                                                 MQTTSuccessFailReasonCode_t reasonCode );

/**
 * @brief Validate Publish Ack Reason Code
 *
 * @param[in] reasonCode Reason Code to validate
 * @param[in] packetType Packet Type byte of the publish ack packet. (PUBACK, PUBREC, PUBREL, PUBCOMP)
 *
 * @return #MQTTBadParameter if invalid parameters are passed;
 * #MQTTSuccess otherwise
 */
static MQTTStatus_t validatePublishAckReasonCode( MQTTSuccessFailReasonCode_t reasonCode,
                                                  uint8_t packetType );

/**
 * @brief Send the disconnect packet without copying the reason code and properties in
 * the buffer.
 *
 * @param[in] pContext MQTT Connection context.
 * @param[in] pReasonCode Optional reason code to be sent in the Disconnect packet.
 * @param[in] remainingLength Remaining length of the packet.
 * @param[in] pPropertyBuilder MQTT Disconnect property builder.
 *
 *
 * @return #MQTTSendFailed if transport send during resend failed;
 * #MQTTSuccess otherwise.
 */

static MQTTStatus_t sendDisconnectWithoutCopy( MQTTContext_t * pContext,
                                               const MQTTSuccessFailReasonCode_t * pReasonCode,
                                               uint32_t remainingLength,
                                               const MQTTPropBuilder_t * pPropertyBuilder );

/**
 * @brief Handle Incoming Disconnect
 *
 * @param[in] pContext MQTT Connection context.
 * @param[in] pIncomingPacket Information of incoming packet
 *
 * @return #MQTTSuccess, #MQTTBadResponse, #MQTTBadParameter, #MQTTEventCallbackFailed,
 */
static MQTTStatus_t handleIncomingDisconnect( MQTTContext_t * pContext,
                                              MQTTPacketInfo_t * pIncomingPacket );

/*-----------------------------------------------------------*/

static bool matchEndWildcardsSpecialCases( const char * pTopicFilter,
                                           uint16_t topicFilterLength,
                                           uint16_t filterIndex )
{
    bool matchFound = false;

    assert( pTopicFilter != NULL );
    assert( topicFilterLength != 0U );

    /* Check if the topic filter has 2 remaining characters and it ends in
     * "/#". This check handles the case to match filter "sport/#" with topic
     * "sport". The reason is that the '#' wildcard represents the parent and
     * any number of child levels in the topic name. */
    if( ( topicFilterLength >= 3U ) &&
        ( filterIndex == ( topicFilterLength - 3U ) ) &&
        ( pTopicFilter[ filterIndex + 1U ] == '/' ) &&
        ( pTopicFilter[ filterIndex + 2U ] == '#' ) )

    {
        matchFound = true;
    }

    /* Check if the next character is "#" or "+" and the topic filter ends in
     * "/#" or "/+". This check handles the cases to match:
     *
     * - Topic filter "sport/+" with topic "sport/".
     * - Topic filter "sport/#" with topic "sport/".
     */
    if( ( filterIndex == ( topicFilterLength - 2U ) ) &&
        ( pTopicFilter[ filterIndex ] == '/' ) )
    {
        /* Check that the last character is a wildcard. */
        matchFound = ( pTopicFilter[ filterIndex + 1U ] == '+' ) ||
                     ( pTopicFilter[ filterIndex + 1U ] == '#' );
    }

    return matchFound;
}

/*-----------------------------------------------------------*/

static bool matchWildcards( const char * pTopicName,
                            uint16_t topicNameLength,
                            const char * pTopicFilter,
                            uint16_t topicFilterLength,
                            uint16_t * pNameIndex,
                            uint16_t * pFilterIndex,
                            bool * pMatch )
{
    bool shouldStopMatching = false;
    bool locationIsValidForWildcard;
    uint16_t nameIndex;

    assert( pTopicName != NULL );
    assert( topicNameLength != 0U );
    assert( pTopicFilter != NULL );
    assert( topicFilterLength != 0U );
    assert( pNameIndex != NULL );
    assert( pFilterIndex != NULL );
    assert( pMatch != NULL );

    nameIndex = *pNameIndex;

    /* Wild card in a topic filter is only valid either at the starting position
     * or when it is preceded by a '/'. */
    locationIsValidForWildcard = ( *pFilterIndex == 0u ) ||
                                 ( pTopicFilter[ *pFilterIndex - 1U ] == '/' );

    if( ( pTopicFilter[ *pFilterIndex ] == '+' ) && ( locationIsValidForWildcard == true ) )
    {
        bool nextLevelExistsInTopicName = false;
        bool nextLevelExistsinTopicFilter = false;

        /* Move topic name index to the end of the current level. The end of the
         * current level is identified by the last character before the next level
         * separator '/'. */
        while( nameIndex < topicNameLength )
        {
            /* Exit the loop if we hit the level separator. */
            if( pTopicName[ nameIndex ] == '/' )
            {
                nextLevelExistsInTopicName = true;
                break;
            }

            nameIndex += 1U;
        }

        /* Determine if the topic filter contains a child level after the current level
         * represented by the '+' wildcard. */
        if( ( *pFilterIndex < ( topicFilterLength - 1U ) ) &&
            ( pTopicFilter[ *pFilterIndex + 1U ] == '/' ) )
        {
            nextLevelExistsinTopicFilter = true;
        }

        /* If the topic name contains a child level but the topic filter ends at
         * the current level, then there does not exist a match. */
        if( ( nextLevelExistsInTopicName == true ) &&
            ( nextLevelExistsinTopicFilter == false ) )
        {
            *pMatch = false;
            shouldStopMatching = true;
        }

        /* If the topic name and topic filter have child levels, then advance the
         * filter index to the level separator in the topic filter, so that match
         * can be performed in the next level.
         * Note: The name index already points to the level separator in the topic
         * name. */
        else if( nextLevelExistsInTopicName == true )
        {
            ( *pFilterIndex )++;
        }
        else
        {
            /* If we have reached here, the the loop terminated on the
             * ( nameIndex < topicNameLength) condition, which means that have
             * reached past the end of the topic name, and thus, we decrement the
             * index to the last character in the topic name. */
            /* coverity[integer_overflow] */
            nameIndex -= ( uint16_t ) 1U;
        }
    }

    /* '#' matches everything remaining in the topic name. It must be the
     * last character in a topic filter. */
    else if( ( pTopicFilter[ *pFilterIndex ] == '#' ) &&
             ( *pFilterIndex == ( topicFilterLength - 1U ) ) &&
             ( locationIsValidForWildcard == true ) )
    {
        /* Subsequent characters don't need to be checked for the
         * multi-level wildcard. */
        *pMatch = true;
        shouldStopMatching = true;
    }
    else
    {
        /* Any character mismatch other than '+' or '#' means the topic
         * name does not match the topic filter. */
        *pMatch = false;
        shouldStopMatching = true;
    }

    *pNameIndex = nameIndex;

    return shouldStopMatching;
}

/*-----------------------------------------------------------*/

static bool matchTopicFilter( const char * pTopicName,
                              uint16_t topicNameLength,
                              const char * pTopicFilter,
                              uint16_t topicFilterLength )
{
    bool matchFound = false, shouldStopMatching = false;
    uint16_t nameIndex = 0, filterIndex = 0;

    assert( pTopicName != NULL );
    assert( topicNameLength != 0 );
    assert( pTopicFilter != NULL );
    assert( topicFilterLength != 0 );

    while( ( nameIndex < topicNameLength ) && ( filterIndex < topicFilterLength ) )
    {
        /* Check if the character in the topic name matches the corresponding
         * character in the topic filter string. */
        if( pTopicName[ nameIndex ] == pTopicFilter[ filterIndex ] )
        {
            /* If the topic name has been consumed but the topic filter has not
             * been consumed, match for special cases when the topic filter ends
             * with wildcard character. */
            if( nameIndex == ( topicNameLength - 1U ) )
            {
                matchFound = matchEndWildcardsSpecialCases( pTopicFilter,
                                                            topicFilterLength,
                                                            filterIndex );
            }
        }
        else
        {
            /* Check for matching wildcards. */
            shouldStopMatching = matchWildcards( pTopicName,
                                                 topicNameLength,
                                                 pTopicFilter,
                                                 topicFilterLength,
                                                 &nameIndex,
                                                 &filterIndex,
                                                 &matchFound );
        }

        if( ( matchFound == true ) || ( shouldStopMatching == true ) )
        {
            break;
        }

        /* Increment indexes. */
        nameIndex++;
        filterIndex++;
    }

    if( matchFound == false )
    {
        /* If the end of both strings has been reached, they match. This represents the
         * case when the topic filter contains the '+' wildcard at a non-starting position.
         * For example, when matching either of "sport/+/player" OR "sport/hockey/+" topic
         * filters with "sport/hockey/player" topic name. */
        matchFound = ( nameIndex == topicNameLength ) &&
                     ( filterIndex == topicFilterLength );
    }

    return matchFound;
}

/*-----------------------------------------------------------*/

static int32_t sendMessageVector( MQTTContext_t * pContext,
                                  TransportOutVector_t * pIoVec,
                                  size_t ioVecCount )
{
    int32_t sendResult;
    uint32_t startTime;
    TransportOutVector_t * pIoVectIterator;
    size_t vectorsToBeSent = ioVecCount;
    uint32_t bytesToSend = 0U;
    int32_t bytesSentOrError = 0;

    assert( pContext != NULL );
    assert( pIoVec != NULL );
    assert( pContext->getTime != NULL );
    /* Send must always be defined */
    assert( pContext->transportInterface.send != NULL );

    /* Count the total number of bytes to be sent as outlined in the vector. */
    for( pIoVectIterator = pIoVec; pIoVectIterator <= &( pIoVec[ ioVecCount - 1U ] ); pIoVectIterator++ )
    {
        /* Before calling this function, the caller has checked that these below conditions
         * are true. */
        assert( !CHECK_SIZE_T_OVERFLOWS_32BIT( pIoVectIterator->iov_len ) );
        assert( !ADDITION_WILL_OVERFLOW_U32( bytesToSend, pIoVectIterator->iov_len ) );
        assert( pIoVectIterator->iov_len <= ( MQTT_MAX_PACKET_SIZE - bytesToSend ) );

        bytesToSend += ( uint32_t ) pIoVectIterator->iov_len;
    }

    /* Reset the iterator to point to the first entry in the array. */
    pIoVectIterator = pIoVec;

    /* Note the start time. */
    startTime = pContext->getTime();

    while( ( bytesSentOrError < ( int32_t ) bytesToSend ) && ( bytesSentOrError >= 0 ) )
    {
        if( pContext->transportInterface.writev != NULL )
        {
            sendResult = pContext->transportInterface.writev( pContext->transportInterface.pNetworkContext,
                                                              pIoVectIterator,
                                                              vectorsToBeSent );
        }
        else
        {
            sendResult = pContext->transportInterface.send( pContext->transportInterface.pNetworkContext,
                                                            pIoVectIterator->iov_base,
                                                            pIoVectIterator->iov_len );
        }

        if( sendResult > 0 )
        {
            /* It is a bug in the application's transport send implementation if
             * more bytes than expected are sent. */
            assert( sendResult <= ( ( int32_t ) bytesToSend - bytesSentOrError ) );

            bytesSentOrError += sendResult;

            /* Set last transmission time. */
            pContext->lastPacketTxTime = pContext->getTime();

            LogDebug( ( "sendMessageVector: Bytes Sent=%ld, Bytes Remaining=%lu",
                        ( long int ) sendResult,
                        ( unsigned long ) ( bytesToSend - ( size_t ) bytesSentOrError ) ) );
        }
        else if( sendResult < 0 )
        {
            bytesSentOrError = sendResult;
            LogError( ( "sendMessageVector: Unable to send packet: Network Error." ) );

            if( pContext->connectStatus == MQTTConnected )
            {
                pContext->connectStatus = MQTTDisconnectPending;
            }
        }
        else
        {
            /* MISRA Empty body */
        }

        /* Update the send pointer to the correct vector and offset. Here, it is fine
         * to cast iov_len (size_t) to int32_t since we have verified that, individually,
         * they all must be smaller than MQTT_MAX_PACKET_SIZE. */
        while( ( pIoVectIterator <= &( pIoVec[ ioVecCount - 1U ] ) ) &&
               ( sendResult >= ( int32_t ) pIoVectIterator->iov_len ) )
        {
            sendResult -= ( int32_t ) pIoVectIterator->iov_len;
            pIoVectIterator++;
            /* Update the number of vector which are yet to be sent. */
            vectorsToBeSent--;
        }

        /* Some of the bytes from this vector were sent as well, update the length
         * and the pointer to data in this vector. One branch in the following
         * condition logically cannot be reached as the iterator would always be
         * bounded if the sendResult is positive. If it were not then the assert
         * above in the function will be triggered and the flow will never reach
         * here. Hence for that sake the branches on this condition are excluded
         * from coverage analysis */
        if( ( sendResult > 0 ) &&
            ( pIoVectIterator <= &( pIoVec[ ioVecCount - 1U ] ) ) ) /* LCOV_EXCL_BR_LINE */
        {
            pIoVectIterator->iov_base = ( const void * ) &( ( ( const uint8_t * ) pIoVectIterator->iov_base )[ sendResult ] );
            pIoVectIterator->iov_len -= ( size_t ) sendResult;
        }

        /* Check for timeout. */
        if( ( bytesSentOrError < ( int32_t ) bytesToSend ) &&
            ( bytesSentOrError >= 0 ) &&
            ( calculateElapsedTime( pContext->getTime(), startTime ) > MQTT_SEND_TIMEOUT_MS ) )
        {
            LogError( ( "sendMessageVector: Unable to send remaining packet: Timed out." ) );
            break;
        }
    }

    return bytesSentOrError;
}

static int32_t sendBuffer( MQTTContext_t * pContext,
                           const uint8_t * pBufferToSend,
                           size_t bytesToSend )
{
    int32_t sendResult;
    uint32_t startTime;
    int32_t bytesSentOrError = 0;
    const uint8_t * pIndex = pBufferToSend;
    int32_t localCopyBytesToSend;

    assert( pContext != NULL );
    assert( pContext->getTime != NULL );
    assert( pContext->transportInterface.send != NULL );
    assert( pIndex != NULL );
    assert( CHECK_SIZE_T_OVERFLOWS_32BIT( bytesToSend ) != true );

    /* Since this function is always called to send one MQTT packet at
     * a time, we can assert on the following. */
    assert( bytesToSend <= MQTT_MAX_PACKET_SIZE );

    /* As we asserted that bytes to send variable must be smaller than
    * MQTT max packet length, it can comfortably fit in an int32_t. */
    localCopyBytesToSend = ( int32_t ) bytesToSend;

    /* Set the timeout. */
    startTime = pContext->getTime();

    while( ( bytesSentOrError < localCopyBytesToSend ) && ( bytesSentOrError >= 0 ) )
    {
        /* Safe to cast as the value will always be positive and will fit in an int32_t and hence
         * in uint32_t. */
        int32_t i32RemainingBytes = localCopyBytesToSend - bytesSentOrError;
        uint32_t remainingBytesToSend = ( uint32_t ) i32RemainingBytes;

        if( CHECK_U32T_OVERFLOWS_SIZE_T( remainingBytesToSend ) )
        {
            LogError( ( "Remaining bytes (%" PRIu32 ") will overflow size_t variable.", remainingBytesToSend ) );
            /* More details at: https://github.com/FreeRTOS/coreMQTT/blob/main/MISRA.md#rule-143 */
            /* coverity[misra_c_2012_rule_14_3_violation] */
            sendResult = -1;
        }
        else
        {
            size_t safeRemainingBytesToSend = ( size_t ) remainingBytesToSend;
            sendResult = pContext->transportInterface.send( pContext->transportInterface.pNetworkContext,
                                                            pIndex,
                                                            safeRemainingBytesToSend );
        }

        if( sendResult > 0 )
        {
            /* It is a bug in the application's transport send implementation if
             * more bytes than expected are sent. */
            assert( sendResult <= ( localCopyBytesToSend - bytesSentOrError ) );

            bytesSentOrError += sendResult;
            pIndex = &pIndex[ sendResult ];

            /* Set last transmission time. */
            pContext->lastPacketTxTime = pContext->getTime();

            LogDebug( ( "sendBuffer: Bytes Sent=%ld, Bytes Remaining=%lu",
                        ( long int ) sendResult,
                        ( unsigned long ) ( localCopyBytesToSend - bytesSentOrError ) ) );
        }
        else if( sendResult < 0 )
        {
            bytesSentOrError = sendResult;
            LogError( ( "sendBuffer: Unable to send packet: Network Error." ) );

            if( pContext->connectStatus == MQTTConnected )
            {
                pContext->connectStatus = MQTTDisconnectPending;
            }
        }
        else
        {
            /* MISRA Empty body */
        }

        /* Check for timeout. */
        if( calculateElapsedTime( pContext->getTime(), startTime ) >= ( MQTT_SEND_TIMEOUT_MS ) )
        {
            LogError( ( "sendBuffer: Unable to send packet: Timed out." ) );
            break;
        }
    }

    return bytesSentOrError;
}

/*-----------------------------------------------------------*/

static uint32_t calculateElapsedTime( uint32_t later,
                                      uint32_t start )
{
    return later - start;
}

/*-----------------------------------------------------------*/

static MQTTPubAckType_t getAckFromPacketType( uint8_t packetType )
{
    MQTTPubAckType_t ackType = MQTTPuback;

    switch( packetType )
    {
        case MQTT_PACKET_TYPE_PUBACK:
            ackType = MQTTPuback;
            break;

        case MQTT_PACKET_TYPE_PUBREC:
            ackType = MQTTPubrec;
            break;

        case MQTT_PACKET_TYPE_PUBREL:
            ackType = MQTTPubrel;
            break;

        default:

            /* This function is only called after checking the type is one of
             * the above four values, so packet type must be PUBCOMP here. */
            assert( packetType == MQTT_PACKET_TYPE_PUBCOMP );
            ackType = MQTTPubcomp;
            break;
    }

    return ackType;
}

/*-----------------------------------------------------------*/

static int32_t recvExact( MQTTContext_t * pContext,
                          size_t bytesToRecv )
{
    uint8_t * pIndex = NULL;
    size_t bytesRemaining = bytesToRecv;
    int32_t totalBytesRecvd = 0, bytesRecvd;
    uint32_t lastDataRecvTimeMs = 0U, timeSinceLastRecvMs = 0U;
    TransportRecv_t recvFunc = NULL;
    MQTTGetCurrentTimeFunc_t getTimeStampMs = NULL;
    bool receiveError = false;

    assert( pContext != NULL );
    assert( bytesToRecv <= pContext->networkBuffer.size );
    assert( pContext->getTime != NULL );
    assert( pContext->transportInterface.recv != NULL );
    assert( pContext->networkBuffer.pBuffer != NULL );

    pIndex = pContext->networkBuffer.pBuffer;
    recvFunc = pContext->transportInterface.recv;
    getTimeStampMs = pContext->getTime;

    /* Part of the MQTT packet has been read before calling this function. */
    lastDataRecvTimeMs = getTimeStampMs();

    while( ( bytesRemaining > 0U ) && ( receiveError == false ) )
    {
        bytesRecvd = recvFunc( pContext->transportInterface.pNetworkContext,
                               pIndex,
                               bytesRemaining );

        if( bytesRecvd < 0 )
        {
            LogError( ( "Network error while receiving packet: ReturnCode=%ld.",
                        ( long int ) bytesRecvd ) );
            totalBytesRecvd = bytesRecvd;
            receiveError = true;

            MQTT_PRE_STATE_UPDATE_HOOK( pContext );

            if( pContext->connectStatus == MQTTConnected )
            {
                pContext->connectStatus = MQTTDisconnectPending;
            }

            MQTT_POST_STATE_UPDATE_HOOK( pContext );
        }
        else if( bytesRecvd > 0 )
        {
            /* Reset the starting time as we have received some data from the network. */
            lastDataRecvTimeMs = getTimeStampMs();

            /* It is a bug in the application's transport receive implementation
             * if more bytes than expected are received. To avoid a possible
             * overflow in converting bytesRemaining from unsigned to signed,
             * this assert must exist after the check for bytesRecvd being
             * negative. */
            assert( ( size_t ) bytesRecvd <= bytesRemaining );

            bytesRemaining -= ( size_t ) bytesRecvd;
            totalBytesRecvd += ( int32_t ) bytesRecvd;
            /* Increment the index. */
            pIndex = &pIndex[ bytesRecvd ];
            LogDebug( ( "BytesReceived=%ld, BytesRemaining=%lu, TotalBytesReceived=%ld.",
                        ( long int ) bytesRecvd,
                        ( unsigned long ) bytesRemaining,
                        ( long int ) totalBytesRecvd ) );
        }
        else
        {
            /* No bytes were read from the network. */
            timeSinceLastRecvMs = calculateElapsedTime( getTimeStampMs(), lastDataRecvTimeMs );

            /* Check for timeout if we have been waiting to receive any byte on the network. */
            if( timeSinceLastRecvMs >= MQTT_RECV_POLLING_TIMEOUT_MS )
            {
                LogError( ( "Unable to receive packet: Timed out in transport recv." ) );
                receiveError = true;
            }
        }
    }

    return totalBytesRecvd;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t receiveConnackPacket( MQTTContext_t * pContext,
                                          MQTTPacketInfo_t incomingPacket )
{
    MQTTStatus_t status = MQTTSuccess;
    int32_t bytesReceived = 0;
    size_t bytesToReceive = 0U;

    assert( pContext != NULL );
    assert( pContext->networkBuffer.pBuffer != NULL );
    assert( incomingPacket.type == MQTT_PACKET_TYPE_CONNACK );
    assert( incomingPacket.remainingLength < MQTT_REMAINING_LENGTH_INVALID );
    assert( !CHECK_U32T_OVERFLOWS_SIZE_T( incomingPacket.remainingLength ) );

    if( incomingPacket.remainingLength > pContext->networkBuffer.size )
    {
        LogError( ( "Incoming packet bigger than the application provided network buffer. Cannot "
                    "handle this packet as MQTT spec doesn't allow 'dropping' packets. Application "
                    "must provide a bigger buffer to handle such packets." ) );
        status = MQTTRecvFailed;
    }
    else
    {
        bytesToReceive = incomingPacket.remainingLength;
        bytesReceived = recvExact( pContext, bytesToReceive );

        if( bytesReceived == ( int32_t ) bytesToReceive )
        {
            /* Receive successful, bytesReceived == bytesToReceive. */
            LogDebug( ( "Packet received. ReceivedBytes=%ld.",
                        ( long int ) bytesReceived ) );
        }
        else
        {
            LogError( ( "Packet reception failed. ReceivedBytes=%ld, "
                        "ExpectedBytes=%lu.",
                        ( long int ) bytesReceived,
                        ( unsigned long ) bytesToReceive ) );
            status = MQTTRecvFailed;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static uint8_t getAckTypeToSend( MQTTPublishState_t state )
{
    uint8_t packetTypeByte = 0U;

    switch( state )
    {
        case MQTTPubAckSend:
            packetTypeByte = MQTT_PACKET_TYPE_PUBACK;
            break;

        case MQTTPubRecSend:
            packetTypeByte = MQTT_PACKET_TYPE_PUBREC;
            break;

        case MQTTPubRelSend:
            packetTypeByte = MQTT_PACKET_TYPE_PUBREL;
            break;

        case MQTTPubCompSend:
            packetTypeByte = MQTT_PACKET_TYPE_PUBCOMP;
            break;

        default:
            /* Take no action for states that do not require sending an ack. */
            break;
    }

    return packetTypeByte;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t sendPublishAcks( MQTTContext_t * pContext,
                                     uint16_t packetId,
                                     MQTTPublishState_t publishState )
{
    MQTTStatus_t status = MQTTSuccess;
    MQTTPublishState_t newState = MQTTStateNull;
    int32_t sendResult = 0;
    uint8_t packetTypeByte = 0U;
    MQTTPubAckType_t packetType;
    MQTTFixedBuffer_t localBuffer;
    MQTTConnectionStatus_t connectStatus;
    uint8_t pubAckPacket[ MQTT_PUBLISH_ACK_PACKET_SIZE ];

    localBuffer.pBuffer = pubAckPacket;
    localBuffer.size = MQTT_PUBLISH_ACK_PACKET_SIZE;

    assert( pContext != NULL );

    packetTypeByte = getAckTypeToSend( publishState );

    if( packetTypeByte != 0U )
    {
        packetType = getAckFromPacketType( packetTypeByte );

        /* TODO: check whether this should be sent with user properties and/or reason code. */
        status = MQTT_SerializeAck( &localBuffer,
                                    packetTypeByte,
                                    packetId,
                                    NULL,
                                    NULL );

        if( status == MQTTSuccess )
        {
            MQTT_PRE_STATE_UPDATE_HOOK( pContext );

            connectStatus = pContext->connectStatus;

            if( connectStatus != MQTTConnected )
            {
                status = ( connectStatus == MQTTNotConnected ) ? MQTTStatusNotConnected : MQTTStatusDisconnectPending;
            }

            if( status == MQTTSuccess )
            {
                /* Here, we are not using the vector approach for efficiency. There is just one buffer
                 * to be sent which can be achieved with a normal send call. */
                sendResult = sendBuffer( pContext,
                                         localBuffer.pBuffer,
                                         MQTT_PUBLISH_ACK_PACKET_SIZE );

                if( sendResult < ( int32_t ) MQTT_PUBLISH_ACK_PACKET_SIZE )
                {
                    status = MQTTSendFailed;
                }
            }

            MQTT_POST_STATE_UPDATE_HOOK( pContext );
        }

        if( status == MQTTSuccess )
        {
            pContext->controlPacketSent = true;

            MQTT_PRE_STATE_UPDATE_HOOK( pContext );

            status = MQTT_UpdateStateAck( pContext,
                                          packetId,
                                          packetType,
                                          MQTT_SEND,
                                          &newState );

            MQTT_POST_STATE_UPDATE_HOOK( pContext );

            if( status != MQTTSuccess )
            {
                LogError( ( "Failed to update state of publish %hu.",
                            ( unsigned short ) packetId ) );
            }
        }
        else
        {
            LogError( ( "Failed to send ACK packet: PacketType=%02x, SentBytes=%ld, "
                        "PacketSize=%lu.",
                        ( unsigned int ) packetTypeByte, ( long int ) sendResult,
                        MQTT_PUBLISH_ACK_PACKET_SIZE ) );
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t handleKeepAlive( MQTTContext_t * pContext )
{
    MQTTStatus_t status = MQTTSuccess;
    uint32_t now = 0U;
    uint32_t packetTxTimeoutMs = 0U;
    uint32_t lastPacketTxTime = 0U;

    assert( pContext != NULL );
    assert( pContext->getTime != NULL );

    now = pContext->getTime();

    packetTxTimeoutMs = 1000U * ( uint32_t ) pContext->keepAliveIntervalSec;

    if( PACKET_TX_TIMEOUT_MS < packetTxTimeoutMs )
    {
        packetTxTimeoutMs = PACKET_TX_TIMEOUT_MS;
    }

    /* If keep alive interval is 0, it is disabled. */
    if( pContext->waitingForPingResp == true )
    {
        /* Has time expired? */
        if( calculateElapsedTime( now, pContext->pingReqSendTimeMs ) >
            MQTT_PINGRESP_TIMEOUT_MS )
        {
            status = MQTTKeepAliveTimeout;
        }
    }
    else
    {
        MQTT_PRE_STATE_UPDATE_HOOK( pContext );
        lastPacketTxTime = pContext->lastPacketTxTime;
        MQTT_POST_STATE_UPDATE_HOOK( pContext );

        if( ( packetTxTimeoutMs != 0U ) && ( calculateElapsedTime( now, lastPacketTxTime ) >= packetTxTimeoutMs ) )
        {
            status = MQTT_Ping( pContext );
        }
        else
        {
            const uint32_t timeElapsed = calculateElapsedTime( now, pContext->lastPacketRxTime );

            if( ( timeElapsed != 0U ) && ( timeElapsed >= PACKET_RX_TIMEOUT_MS ) )
            {
                status = MQTT_Ping( pContext );
            }
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t sendPublishAcksWithoutProperty( MQTTContext_t * pContext,
                                                    uint16_t packetId,
                                                    MQTTPublishState_t publishState )
{
    MQTTStatus_t status = MQTTSuccess;
    MQTTPublishState_t newState = MQTTStateNull;
    int32_t sendResult = 0;
    uint8_t packetTypeByte = 0U;
    MQTTPubAckType_t packetType;
    MQTTFixedBuffer_t localBuffer;
    MQTTConnectionStatus_t connectStatus;
    uint8_t pubAckPacket[ MQTT_PUBLISH_ACK_PACKET_SIZE ];

    localBuffer.pBuffer = pubAckPacket;
    localBuffer.size = MQTT_PUBLISH_ACK_PACKET_SIZE;

    assert( pContext != NULL );

    packetTypeByte = getAckTypeToSend( publishState );

    LogDebug( ( "Got ACK packet type 0x%02x [pkt ID: %hu] for the publish state 0x%02x",
                packetTypeByte,
                packetId,
                publishState ) );

    if( packetTypeByte != 0U )
    {
        packetType = getAckFromPacketType( packetTypeByte );

        status = MQTT_SerializeAck( &localBuffer,
                                    packetTypeByte,
                                    packetId,
                                    NULL,
                                    NULL );

        if( MQTT_PUBLISH_ACK_PACKET_SIZE > pContext->connectionProperties.serverMaxPacketSize )
        {
            LogError( ( "Packet size is greater than the allowed maximum packet size." ) );
            status = MQTTBadParameter;
        }

        if( status == MQTTSuccess )
        {
            MQTT_PRE_STATE_UPDATE_HOOK( pContext );
            {
                TransportOutVector_t vector;
                MQTTVec_t mqttVec;
                vector.iov_base = localBuffer.pBuffer;
                vector.iov_len = MQTT_PUBLISH_ACK_PACKET_SIZE;
                mqttVec.pVector = &vector;
                mqttVec.vectorLen = 1U;

                connectStatus = pContext->connectStatus;

                if( connectStatus != MQTTConnected )
                {
                    status = ( connectStatus == MQTTNotConnected ) ? MQTTStatusNotConnected : MQTTStatusDisconnectPending;
                }

                if( ( status == MQTTSuccess ) &&
                    ( packetTypeByte != MQTT_PACKET_TYPE_PUBACK ) &&
                    ( packetTypeByte != MQTT_PACKET_TYPE_PUBCOMP ) &&
                    ( pContext->storeFunction != NULL ) &&
                    ( pContext->storeFunction( pContext, SET_INCOMING_PUB_FLAG( packetId ), &mqttVec ) != true ) )
                {
                    status = MQTTPublishStoreFailed;
                }

                if( status == MQTTSuccess )
                {
                    LogDebug( ( "Sending ACK packet: PacketType=%02x, PacketID=%hu.",
                                ( unsigned int ) packetTypeByte, ( unsigned short ) packetId ) );

                    /* Here, we are not using the vector approach for efficiency. There is just one buffer
                     * to be sent which can be achieved with a normal send call. */
                    sendResult = sendBuffer( pContext,
                                             localBuffer.pBuffer,
                                             MQTT_PUBLISH_ACK_PACKET_SIZE );

                    if( sendResult < ( int32_t ) MQTT_PUBLISH_ACK_PACKET_SIZE )
                    {
                        status = MQTTSendFailed;
                    }
                }
            }
            MQTT_POST_STATE_UPDATE_HOOK( pContext );
        }

        if( status == MQTTSuccess )
        {
            pContext->controlPacketSent = true;

            MQTT_PRE_STATE_UPDATE_HOOK( pContext );
            {
                status = MQTT_UpdateStateAck( pContext,
                                              packetId,
                                              packetType,
                                              MQTT_SEND,
                                              &newState );
            }
            MQTT_POST_STATE_UPDATE_HOOK( pContext );

            if( status != MQTTSuccess )
            {
                LogError( ( "Failed to update state of publish %hu.",
                            ( unsigned short ) packetId ) );
            }
        }
        else
        {
            LogError( ( "Failed to send ACK packet: PacketType=%02x, SentBytes=%ld, "
                        "PacketSize=%lu.",
                        ( unsigned int ) packetTypeByte, ( long int ) sendResult,
                        MQTT_PUBLISH_ACK_PACKET_SIZE ) );
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

/**
 * @brief Build the IO vector for a publish ACK with properties and send it.
 * Returns MQTTSuccess, MQTTSendFailed, MQTTBadParameter, or MQTTPublishStoreFailed.
 */
static MQTTStatus_t buildAndSendAckWithProps( MQTTContext_t * pContext,
                                              uint8_t packetTypeByte,
                                              uint16_t packetId,
                                              MQTTSuccessFailReasonCode_t reasonCode,
                                              uint32_t remainingLength,
                                              size_t ackPropertyLength )
{
    MQTTStatus_t status = MQTTSuccess;
    int32_t bytesSentOrError;
    size_t ioVectorLength = 0U;
    uint32_t totalMessageLength = 0U;
    uint8_t propertyLength[ 4U ];
    uint8_t pubAckHeader[ 8U ];
    TransportOutVector_t pIoVector[ 3U ];
    uint8_t * pIndex = pubAckHeader;
    TransportOutVector_t * iterator = pIoVector;

    pIndex = serializeAckFixed( pIndex, packetTypeByte, packetId, remainingLength, reasonCode );
    iterator->iov_base = pubAckHeader;
    /* coverity[misra_c_2012_rule_18_2_violation] */
    /* coverity[misra_c_2012_rule_10_8_violation] */
    iterator->iov_len = ( size_t ) ( pIndex - pubAckHeader );
    assert( iterator->iov_len < MQTT_MAX_PACKET_SIZE );
    totalMessageLength += ( uint32_t ) iterator->iov_len;
    iterator++;
    ioVectorLength++;

    /* Encode property length (0 if no properties). */
    pIndex = encodeVariableLength( propertyLength, ( uint32_t ) ackPropertyLength );
    iterator->iov_base = propertyLength;
    /* coverity[misra_c_2012_rule_18_2_violation] */
    /* coverity[misra_c_2012_rule_10_8_violation] */
    iterator->iov_len = ( size_t ) ( pIndex - propertyLength );
    assert( iterator->iov_len < MQTT_MAX_PACKET_SIZE );
    assert( ADDITION_WILL_OVERFLOW_U32( totalMessageLength, iterator->iov_len ) == false );
    totalMessageLength += ( uint32_t ) iterator->iov_len;
    iterator++;
    ioVectorLength++;

    if( ( pContext->ackPropsBuffer.pBuffer != NULL ) && ( ackPropertyLength != 0U ) )
    {
        iterator->iov_base = pContext->ackPropsBuffer.pBuffer;
        iterator->iov_len = pContext->ackPropsBuffer.currentIndex;
        assert( iterator->iov_len < MQTT_MAX_PACKET_SIZE );
        assert( ADDITION_WILL_OVERFLOW_U32( totalMessageLength, iterator->iov_len ) == false );
        totalMessageLength += ( uint32_t ) iterator->iov_len;
        iterator++;
        ioVectorLength++;

        pContext->ackPropsBuffer.currentIndex = 0;
        pContext->ackPropsBuffer.fieldSet = 0;
    }

    if( totalMessageLength > MQTT_MAX_PACKET_SIZE )
    {
        LogError( ( "Total message length cannot be larger than 268435460." ) );
        status = MQTTBadParameter;
    }
    else
    {
        MQTTVec_t mqttVec;
        mqttVec.pVector = pIoVector;
        mqttVec.vectorLen = ioVectorLength;

        if( ( pContext->storeFunction != NULL ) &&
            ( packetTypeByte != MQTT_PACKET_TYPE_PUBACK ) &&
            ( packetTypeByte != MQTT_PACKET_TYPE_PUBCOMP ) &&
            ( pContext->storeFunction( pContext, SET_INCOMING_PUB_FLAG( packetId ), &mqttVec ) != true ) )
        {
            status = MQTTPublishStoreFailed;
        }
    }

    if( status == MQTTSuccess )
    {
        MQTT_PRE_STATE_UPDATE_HOOK( pContext );
        {
            LogDebug( ( "Sending ACK packet: PacketType=%02x, PacketID=%hu.",
                        ( unsigned int ) packetTypeByte, ( unsigned short ) packetId ) );
            bytesSentOrError = sendMessageVector( pContext, pIoVector, ioVectorLength );
        }
        MQTT_POST_STATE_UPDATE_HOOK( pContext );

        if( bytesSentOrError != ( int32_t ) totalMessageLength )
        {
            LogError( ( "Failed to send ACK packet: PacketType=%02x, PacketSize=%" PRIu32,
                        ( unsigned int ) packetTypeByte, remainingLength ) );
            status = MQTTSendFailed;
        }
    }

    return status;
}

static MQTTStatus_t sendPublishAcksWithProperty( MQTTContext_t * pContext,
                                                 uint16_t packetId,
                                                 MQTTPublishState_t publishState,
                                                 MQTTSuccessFailReasonCode_t reasonCode )
{
    MQTTStatus_t status = MQTTSuccess;
    MQTTPublishState_t newState = MQTTStateNull;
    uint8_t packetTypeByte = 0U;
    MQTTPubAckType_t packetType;
    size_t ackPropertyLength = 0U;
    uint32_t remainingLength = 0U;
    uint32_t packetSize = 0U;

    assert( pContext != NULL );

    if( pContext->ackPropsBuffer.pBuffer != NULL )
    {
        assert( !CHECK_SIZE_T_OVERFLOWS_32BIT( pContext->ackPropsBuffer.currentIndex ) &&
                ( pContext->ackPropsBuffer.currentIndex < MQTT_REMAINING_LENGTH_INVALID ) );
        ackPropertyLength = pContext->ackPropsBuffer.currentIndex;
    }

    packetTypeByte = getAckTypeToSend( publishState );

    LogDebug( ( "Got ACK packet type 0x%02x [pkt ID: %hu] for the publish state 0x%02x",
                packetTypeByte, packetId, publishState ) );

    if( packetTypeByte != 0U )
    {
        if( pContext->ackPropsBuffer.currentIndex > 0U )
        {
            status = MQTT_ValidatePublishAckProperties( &pContext->ackPropsBuffer );
        }

        if( status == MQTTSuccess )
        {
            status = validatePublishAckReasonCode( reasonCode, packetTypeByte );
        }

        if( status == MQTTSuccess )
        {
            status = MQTT_GetAckPacketSize( &remainingLength, &packetSize,
                                            pContext->connectionProperties.serverMaxPacketSize,
                                            ackPropertyLength );
        }
    }

    if( ( status == MQTTSuccess ) && ( pContext->connectStatus != MQTTConnected ) )
    {
        status = ( pContext->connectStatus == MQTTNotConnected ) ? MQTTStatusNotConnected : MQTTStatusDisconnectPending;
    }

    if( ( packetTypeByte != 0U ) && ( status == MQTTSuccess ) )
    {
        packetType = getAckFromPacketType( packetTypeByte );

        status = buildAndSendAckWithProps( pContext, packetTypeByte, packetId,
                                           reasonCode, remainingLength, ackPropertyLength );

        if( status == MQTTSuccess )
        {
            pContext->controlPacketSent = true;

            MQTT_PRE_STATE_UPDATE_HOOK( pContext );
            {
                status = MQTT_UpdateStateAck( pContext, packetId, packetType,
                                              MQTT_SEND, &newState );
            }
            MQTT_POST_STATE_UPDATE_HOOK( pContext );

            if( status != MQTTSuccess )
            {
                LogError( ( "Failed to update state of publish %hu.",
                            ( unsigned short ) packetId ) );
            }
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t validatePublishAckReasonCode( MQTTSuccessFailReasonCode_t reasonCode,
                                                  uint8_t packetType )
{
    MQTTStatus_t status = MQTTSuccess;

    switch( reasonCode )
    {
        case MQTT_REASON_PUBACK_SUCCESS:
            status = MQTTSuccess;
            break;

        case MQTT_REASON_PUBACK_NO_MATCHING_SUBSCRIBERS:
        case MQTT_REASON_PUBACK_UNSPECIFIED_ERROR:
        case MQTT_REASON_PUBACK_IMPLEMENTATION_SPECIFIC_ERROR:
        case MQTT_REASON_PUBACK_NOT_AUTHORIZED:
        case MQTT_REASON_PUBACK_TOPIC_NAME_INVALID:
        case MQTT_REASON_PUBACK_PACKET_IDENTIFIER_IN_USE:
        case MQTT_REASON_PUBACK_QUOTA_EXCEEDED:
        case MQTT_REASON_PUBACK_PAYLOAD_FORMAT_INVALID:

            if( ( packetType == MQTT_PACKET_TYPE_PUBACK ) || ( packetType == MQTT_PACKET_TYPE_PUBREC ) )
            {
                status = MQTTSuccess;
            }
            else
            {
                status = MQTTBadParameter;
                LogError( ( "Invalid Reason Code for PUBREL or PUBCOMP packet." ) );
            }

            break;

        case MQTT_REASON_PUBREL_PACKET_IDENTIFIER_NOT_FOUND:

            if( ( packetType == MQTT_PACKET_TYPE_PUBREL ) || ( packetType == MQTT_PACKET_TYPE_PUBCOMP ) )
            {
                status = MQTTSuccess;
            }
            else
            {
                status = MQTTBadParameter;
                LogError( ( "Invalid Reason Code for PUBREC or PUBACK packet." ) );
            }

            break;

        default:
            status = MQTTBadParameter;
            LogError( ( "Invalid Reason Code." ) );
            break;
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t handleIncomingPublish( MQTTContext_t * pContext,
                                           MQTTPacketInfo_t * pIncomingPacket )
{
    MQTTStatus_t status;
    MQTTPublishState_t publishRecordState = MQTTStateNull;
    uint16_t packetIdentifier = 0U;
    MQTTPublishInfo_t publishInfo = { 0 };
    MQTTDeserializedInfo_t deserializedInfo;
    bool duplicatePublish = false;
    MQTTPropBuilder_t propBuffer = { 0 };
    MQTTSuccessFailReasonCode_t reasonCode = MQTT_INVALID_REASON_CODE;
    bool ackPropsAdded = false;

    assert( pContext != NULL );
    assert( pIncomingPacket != NULL );
    assert( pContext->appCallback != NULL );

    status = MQTT_DeserializePublish( pIncomingPacket,
                                      &packetIdentifier,
                                      &publishInfo,
                                      &propBuffer,
                                      pContext->connectionProperties.maxPacketSize,
                                      pContext->connectionProperties.topicAliasMax );

    LogInfo( ( "De-serialized incoming PUBLISH packet: DeserializerResult=%s.",
               MQTT_Status_strerror( status ) ) );

    if( ( status == MQTTSuccess ) &&
        ( pContext->incomingPublishRecords == NULL ) &&
        ( publishInfo.qos > MQTTQoS0 ) )
    {
        LogError( ( "Incoming publish has QoS > MQTTQoS0 but incoming "
                    "publish records have not been initialized. Dropping the "
                    "incoming publish. Please call MQTT_InitStatefulQoS to enable "
                    "use of QoS1 and QoS2 publishes." ) );
        status = MQTTRecvFailed;
    }

    if( status == MQTTSuccess )
    {
        MQTT_PRE_STATE_UPDATE_HOOK( pContext );

        status = MQTT_UpdateStatePublish( pContext,
                                          packetIdentifier,
                                          MQTT_RECEIVE,
                                          publishInfo.qos,
                                          &publishRecordState );

        MQTT_POST_STATE_UPDATE_HOOK( pContext );

        if( status == MQTTSuccess )
        {
            LogInfo( ( "State record updated. New state=%s.",
                       MQTT_State_strerror( publishRecordState ) ) );
        }

        /* Different cases in which an incoming publish with duplicate flag is
         * handled are as listed below.
         * 1. No collision - This is the first instance of the incoming publish
         *    packet received or an earlier received packet state is lost. This
         *    will be handled as a new incoming publish for both QoS1 and QoS2
         *    publishes.
         * 2. Collision - The incoming packet was received before and a state
         *    record is present in the state engine. For QoS1 and QoS2 publishes
         *    this case can happen at 2 different cases and handling is
         *    different.
         *    a. QoS1 - If a PUBACK is not successfully sent for the incoming
         *       publish due to a connection issue, it can result in broker
         *       sending out a duplicate publish with dup flag set, when a
         *       session is reestablished. It can result in a collision in
         *       state engine. This will be handled by processing the incoming
         *       publish as a new publish ignoring the
         *       #MQTTStateCollision status from the state engine. The publish
         *       data is not passed to the application.
         *    b. QoS2 - If a PUBREC is not successfully sent for the incoming
         *       publish or the PUBREC sent is not successfully received by the
         *       broker due to a connection issue, it can result in broker
         *       sending out a duplicate publish with dup flag set, when a
         *       session is reestablished. It can result in a collision in
         *       state engine. This will be handled by ignoring the
         *       #MQTTStateCollision status from the state engine. The publish
         *       data is not passed to the application. */
        else if( status == MQTTStateCollision )
        {
            status = MQTTSuccess;
            duplicatePublish = true;

            /* Calculate the state for the ack packet that needs to be sent out
             * for the duplicate incoming publish. */
            publishRecordState = MQTT_CalculateStatePublish( MQTT_RECEIVE,
                                                             publishInfo.qos );

            LogDebug( ( "Incoming publish packet with packet id %hu already exists.",
                        ( unsigned short ) packetIdentifier ) );

            if( publishInfo.dup == false )
            {
                LogError( ( "DUP flag is 0 for duplicate packet (MQTT-3.3.1.-1)." ) );
            }
        }
        else
        {
            LogError( ( "Error in updating publish state for incoming publish with packet id %hu."
                        " Error is %s",
                        ( unsigned short ) packetIdentifier,
                        MQTT_Status_strerror( status ) ) );
        }
    }

    if( status == MQTTSuccess )
    {
        deserializedInfo.packetIdentifier = packetIdentifier;
        deserializedInfo.pPublishInfo = &publishInfo;
        deserializedInfo.deserializationResult = status;

        /* Invoke application callback to hand the buffer over to application
         * before sending acks. */
        reasonCode = MQTT_INVALID_REASON_CODE;

        if( ( duplicatePublish == false ) ||
            ( publishInfo.qos == MQTTQoS1 ) ) /* Even a duplicate QoS1 packet must be forwarded to the application [MQTT-4.3.2-5]. */
        {
            MQTTPropBuilder_t * pTempPropBuffer = NULL;
            MQTTSuccessFailReasonCode_t * pTempReasonCode = NULL;

            if( publishInfo.qos > MQTTQoS0 )
            {
                pTempPropBuffer = &( pContext->ackPropsBuffer );
                pTempReasonCode = &reasonCode;
            }

            if( pContext->appCallback( pContext, pIncomingPacket, &deserializedInfo,
                                       pTempReasonCode, pTempPropBuffer, &propBuffer ) == false )
            {
                /* TODO: Figure out whether this should block the library
                 * from processing any more packets. */
                status = MQTTEventCallbackFailed;
            }
            else if( publishInfo.qos > MQTTQoS0 )
            {
                if( ( pContext->ackPropsBuffer.pBuffer != NULL ) &&
                    ( CHECK_SIZE_T_OVERFLOWS_32BIT( pContext->ackPropsBuffer.currentIndex ) ||
                      ( pContext->ackPropsBuffer.currentIndex >= MQTT_REMAINING_LENGTH_INVALID ) ) )
                {
                    status = MQTTSendFailed;
                    LogError( ( "Length of properties to be sent must be less than 268435456." ) );
                }
                else
                {
                    /* Send PUBREC or PUBCOMP if necessary. */
                    ackPropsAdded = ( pContext->ackPropsBuffer.pBuffer != NULL ) &&
                                    ( pContext->ackPropsBuffer.currentIndex > 0U );
                }
            }
            else
            {
                /* Nothing to be done. QoS0 incoming publish handled successfully. */
            }
        }

        if( ( status == MQTTSuccess ) && ( publishInfo.qos > MQTTQoS0 ) )
        {
            if( ( ackPropsAdded == false ) && ( reasonCode == MQTT_INVALID_REASON_CODE ) )
            {
                LogTrace( ( "No reason code provided by application. Sending default reason code." ) );
                status = sendPublishAcksWithoutProperty( pContext,
                                                         packetIdentifier,
                                                         publishRecordState );
            }
            else
            {
                LogTrace( ( "Reason code provided by application. Sending reason code." ) );
                status = sendPublishAcksWithProperty( pContext,
                                                      packetIdentifier,
                                                      publishRecordState,
                                                      reasonCode );
            }
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t handlePublishAcks( MQTTContext_t * pContext,
                                       MQTTPacketInfo_t * pIncomingPacket )
{
    MQTTStatus_t status;
    MQTTPublishState_t publishRecordState = MQTTStateNull;
    uint16_t packetIdentifier;
    MQTTPubAckType_t ackType;
    MQTTEventCallback_t appCallback;
    MQTTDeserializedInfo_t deserializedInfo;
    MQTTPropBuilder_t propBuffer = { 0 };
    MQTTPropBuilder_t * pSendProps;
    MQTTSuccessFailReasonCode_t * pSendReasonCode;
    MQTTSuccessFailReasonCode_t reasonCode = MQTT_INVALID_REASON_CODE;
    bool ackPropsAdded;

    MQTTReasonCodeInfo_t incomingReasonCode = { 0 };

    assert( pContext != NULL );
    assert( pIncomingPacket != NULL );
    assert( pContext->appCallback != NULL );

    appCallback = pContext->appCallback;

    ackType = getAckFromPacketType( pIncomingPacket->type );

    status = MQTT_DeserializeAck( pIncomingPacket,
                                  &packetIdentifier,
                                  &incomingReasonCode,
                                  &propBuffer,
                                  &pContext->connectionProperties );

    LogDebug( ( "Ack packet of type %s (packet ID: %" PRIu16 ") deserialized with result: %s.",
                MQTT_GetPacketTypeString( pIncomingPacket->type ),
                packetIdentifier,
                MQTT_Status_strerror( status ) ) );

    if( status == MQTTSuccess )
    {
        MQTT_PRE_STATE_UPDATE_HOOK( pContext );
        {
            status = MQTT_UpdateStateAck( pContext,
                                          packetIdentifier,
                                          ackType,
                                          MQTT_RECEIVE,
                                          &publishRecordState );
        }
        MQTT_POST_STATE_UPDATE_HOOK( pContext );

        if( status == MQTTSuccess )
        {
            LogInfo( ( "State record updated. New state=%s.",
                       MQTT_State_strerror( publishRecordState ) ) );
        }
        else
        {
            LogError( ( "Updating the state engine for packet id %hu"
                        " failed with error %s.",
                        ( unsigned short ) packetIdentifier,
                        MQTT_Status_strerror( status ) ) );
        }
    }

    if( ( status == MQTTSuccess ) &&
        ( pContext->clearFunction != NULL ) )
    {
        /* Outgoing publish QoS1: (Tx) PUBLISH -> (Rx) PUBACK. On receiving PubAck, the packet is acked and can be cleared. */
        if( ackType == MQTTPuback )
        {
            /* Clear the stored publish. */
            pContext->clearFunction( pContext, ( uint32_t ) packetIdentifier );
        }

        /* Outgoing publish QoS2: (Tx) PUBLISH -> (Rx) PUBREC -> (Tx) PUBREL -> (Rx) PUBCOMP. Sender MUST treat the PUBLISH
         * packet as “unacknowledged” until it has received the corresponding PUBREC packet from the receiver [MQTT-4.3.3-3] */
        else if( ackType == MQTTPubrec )
        {
            /* Clear the stored publish. */
            pContext->clearFunction( pContext, ( uint32_t ) packetIdentifier );
        }

        /* Outgoing publish QoS2: Sender MUST treat the PUBREL packet as “unacknowledged” until it has received the corresponding
         * PUBCOMP packet from the receiver [MQTT-4.3.3-5]. */
        else if( ackType == MQTTPubcomp )
        {
            /* Clear the stored PUBREL. */
            pContext->clearFunction( pContext, SET_INCOMING_PUB_FLAG( packetIdentifier ) );
        }

        /* Incoming Publish QoS2: (Rx) PUBLISH -> (Tx) PUBREC -> (Rx) PUBREL -> (Tx) PUBCOMP. Once we receive PUBREL, it means that
         * the broker received and processed the PUBREC packet [MQTT-4.3.3-10]. */
        else if( ackType == MQTTPubrel )
        {
            /* Clear the stored PUBREC. */
            pContext->clearFunction( pContext, SET_INCOMING_PUB_FLAG( packetIdentifier ) );
        }
        /* The following should never happen. The ACK type must be one of the above. */
        else
        {
            assert( false );
            status = MQTTBadResponse;
        }
    }

    if( status == MQTTSuccess )
    {
        deserializedInfo.packetIdentifier = packetIdentifier;
        deserializedInfo.deserializationResult = status;
        deserializedInfo.pPublishInfo = NULL;
        deserializedInfo.pReasonCode = &incomingReasonCode;

        if( ( ackType == MQTTPuback ) || ( ackType == MQTTPubcomp ) )
        {
            /* This is the last packet in PUB-ACK sequence - we will set these
             * to NULL. */
            pSendProps = NULL;
            pSendReasonCode = NULL;
        }
        else
        {
            /* We need to send a response back to the server. Provide application with
             * space to add data. */
            pSendProps = &pContext->ackPropsBuffer;
            pSendReasonCode = &reasonCode;
        }

        /* Invoke application callback to hand the buffer over to application
         * before sending acks. */
        if( appCallback( pContext, pIncomingPacket, &deserializedInfo, pSendReasonCode,
                         pSendProps, &propBuffer ) == false )
        {
            /* TODO: verify whether this should block the recv thread? */
            status = MQTTEventCallbackFailed;
        }
        else if( ( pContext->ackPropsBuffer.pBuffer != NULL ) &&
                 ( CHECK_SIZE_T_OVERFLOWS_32BIT( pContext->ackPropsBuffer.currentIndex ) ||
                   ( pContext->ackPropsBuffer.currentIndex >= MQTT_REMAINING_LENGTH_INVALID ) ) )
        {
            status = MQTTSendFailed;
            LogError( ( "Length of properties to be sent must be less than 268435456." ) );
        }
        else
        {
            /* Send PUBREC or PUBCOMP if necessary. */
            ackPropsAdded = ( pContext->ackPropsBuffer.pBuffer != NULL ) &&
                            ( pContext->ackPropsBuffer.currentIndex > 0U );
        }

        /* No need to call the following functions if the packet that was received was PUBACK or PUBCOMP. */
        if( ( status == MQTTSuccess ) && ( ackType != MQTTPuback ) && ( ackType != MQTTPubcomp ) )
        {
            if( ( ackPropsAdded == false ) && ( reasonCode == MQTT_INVALID_REASON_CODE ) )
            {
                LogTrace( ( "No reason code provided by application. Sending default reason code." ) );
                status = sendPublishAcksWithoutProperty( pContext,
                                                         packetIdentifier,
                                                         publishRecordState );
            }
            else
            {
                LogTrace( ( "Reason code provided by application. Sending reason code." ) );
                status = sendPublishAcksWithProperty( pContext,
                                                      packetIdentifier,
                                                      publishRecordState,
                                                      reasonCode );
            }
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t handleIncomingAck( MQTTContext_t * pContext,
                                       MQTTPacketInfo_t * pIncomingPacket,
                                       bool manageKeepAlive )
{
    MQTTStatus_t status = MQTTBadResponse;
    uint16_t packetIdentifier = MQTT_PACKET_ID_INVALID;
    MQTTDeserializedInfo_t deserializedInfo;

    MQTTEventCallback_t appCallback;

    assert( pContext != NULL );
    assert( pIncomingPacket != NULL );
    assert( pContext->appCallback != NULL );

    appCallback = pContext->appCallback;

    LogTrace( ( "Received packet of type %s.",
                MQTT_GetPacketTypeString( pIncomingPacket->type ) ) );

    switch( pIncomingPacket->type )
    {
        case MQTT_PACKET_TYPE_PUBACK:
        case MQTT_PACKET_TYPE_PUBREC:
        case MQTT_PACKET_TYPE_PUBREL:
        case MQTT_PACKET_TYPE_PUBCOMP:

            /* Handle all the publish acks. The app callback is invoked here. */
            status = handlePublishAcks( pContext, pIncomingPacket );

            break;

        case MQTT_PACKET_TYPE_PINGRESP:
            /* PINGRESP has no payload. Thus reason code and properties are NULL. */
            status = MQTT_DeserializeAck( pIncomingPacket,
                                          &packetIdentifier,
                                          NULL,
                                          NULL,
                                          &pContext->connectionProperties );

            if( status == MQTTSuccess )
            {
                if( manageKeepAlive == true )
                {
                    pContext->waitingForPingResp = false;
                }
                else
                {
                    /* Set fields of deserialized struct. */
                    deserializedInfo.packetIdentifier = packetIdentifier;
                    deserializedInfo.deserializationResult = status;
                    deserializedInfo.pPublishInfo = NULL;

                    if( appCallback( pContext, pIncomingPacket, &deserializedInfo, NULL,
                                     NULL, NULL ) == false )
                    {
                        status = MQTTEventCallbackFailed;
                    }
                }
            }

            break;

        case MQTT_PACKET_TYPE_SUBACK:
        case MQTT_PACKET_TYPE_UNSUBACK:
            /* Deserialize and give these to the app provided callback. */
            status = handleSubUnsubAck( pContext, pIncomingPacket );
            break;

        default:
            /* Bad response from the server. */
            LogError( ( "Unexpected packet type from server: PacketType=%02x.",
                        ( unsigned int ) pIncomingPacket->type ) );
            status = MQTTBadResponse;
            break;
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t handleIncomingDisconnect( MQTTContext_t * pContext,
                                              MQTTPacketInfo_t * pIncomingPacket )
{
    MQTTStatus_t status = MQTTSuccess;
    MQTTDeserializedInfo_t deserializedInfo = { 0 };
    MQTTPropBuilder_t propBuffer = { 0 };
    MQTTReasonCodeInfo_t reasonCode = { 0 };

    assert( pContext != NULL );
    assert( pContext->appCallback != NULL );
    assert( pIncomingPacket != NULL );

    status = MQTT_DeserializeDisconnect( pIncomingPacket,
                                         pContext->connectionProperties.maxPacketSize,
                                         &reasonCode,
                                         &propBuffer );

    if( status == MQTTSuccess )
    {
        deserializedInfo.pReasonCode = &reasonCode;

        if( pContext->appCallback( pContext, pIncomingPacket, &deserializedInfo,
                                   NULL, NULL, &propBuffer ) == false )
        {
            status = MQTTEventCallbackFailed;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t receiveSingleIteration( MQTTContext_t * pContext,
                                            bool manageKeepAlive )
{
    MQTTStatus_t status = MQTTSuccess;
    MQTTPacketInfo_t incomingPacket = { 0 };
    int32_t recvBytes;
    uint32_t totalMQTTPacketLength = 0;

    assert( pContext != NULL );
    assert( pContext->networkBuffer.pBuffer != NULL );

    /* We will store the result in a signed 32 bit value, so we cannot have a
     * buffer bigger than what can fit in a int32_t. 0x7FFFFFFF is 2Gb which should
     * be enough. */
    assert( pContext->networkBuffer.size < 0x7FFFFFFF );

    /* Read as many bytes as possible into the network buffer. */
    recvBytes = pContext->transportInterface.recv( pContext->transportInterface.pNetworkContext,
                                                   &( pContext->networkBuffer.pBuffer[ pContext->index ] ),
                                                   pContext->networkBuffer.size - pContext->index );

    LogTrace( ( "Received %ld bytes from network.",
                ( long int ) recvBytes ) );
    LogTrace( ( "Index is at location: %ld",
                ( long int ) pContext->index ) );
    LogTrace( ( "Remaining buffer capacity: %ld",
                ( long int ) ( pContext->networkBuffer.size - pContext->index ) ) );

    do
    {
        if( recvBytes < 0 )
        {
            /* The receive function has failed. Bubble up the error up to the user. */
            status = MQTTRecvFailed;

            MQTT_PRE_STATE_UPDATE_HOOK( pContext );

            if( pContext->connectStatus == MQTTConnected )
            {
                pContext->connectStatus = MQTTDisconnectPending;
            }

            MQTT_POST_STATE_UPDATE_HOOK( pContext );

            LogTrace( ( "Recv failed with error: %s", strerror( errno ) ) );
        }
        else if( ( recvBytes == 0 ) && ( pContext->index == 0U ) )
        {
            LogTrace( ( "No data available from the network." ) );

            /* No more bytes available since the last read and neither is anything in
             * the buffer. */
            status = MQTTNoDataAvailable;
        }

        /* Either something was received, or there is still data to be processed in the
         * buffer, or both. */
        else
        {
            /* Update the number of bytes in the MQTT fixed buffer. */

            /* No need to check whether the addition will overflow here since the transport
             * interface is supposed to only return less than or equal number of bytes than
             * requested. */
            pContext->index += ( size_t ) recvBytes;

            status = MQTT_ProcessIncomingPacketTypeAndLength( pContext->networkBuffer.pBuffer,
                                                              &( pContext->index ),
                                                              &incomingPacket );

            /* Remaining length can be in the range of 0 -> MQTT_MAX_REMAINING_LENGTH.
             * Header length will be in range of 1 -> 5.
             * Thus, the addition will not overflow when the status is MQTTSuccess. */
            totalMQTTPacketLength = incomingPacket.remainingLength + ( uint32_t ) incomingPacket.headerLength;
        }

        /* No data was received, check for keep alive timeout. */
        if( ( ( status == MQTTSuccess ) ||
              ( status == MQTTNoDataAvailable ) ||
              ( status == MQTTNeedMoreBytes ) ) &&
            ( recvBytes == 0 ) )
        {
            if( manageKeepAlive == true )
            {
                /* Keep the copy of the status to be reset later. */
                MQTTStatus_t statusCopy = status;

                /* Assign status so an error can be bubbled up to application,
                 * but reset it on success. */
                status = handleKeepAlive( pContext );

                if( status == MQTTSuccess )
                {
                    /* Reset the status. */
                    status = statusCopy;
                }
                else
                {
                    LogError( ( "Handling of keep alive failed. Status=%s",
                                MQTT_Status_strerror( status ) ) );
                }
            }
        }
        else
        {
            recvBytes = 0;
        }

        /* Check whether there is data available before processing the packet further. */
        if( ( status == MQTTNeedMoreBytes ) || ( status == MQTTNoDataAvailable ) )
        {
            /* Do nothing as there is nothing to be processed right now. The proper
             * error code will be bubbled up to the user. */
        }
        /* Any other error code. */
        else if( status != MQTTSuccess )
        {
            LogError( ( "Call to receiveSingleIteration failed. Status=%s",
                        MQTT_Status_strerror( status ) ) );
        }
        /* If the MQTT Packet size is bigger than the buffer itself. */
        else if( totalMQTTPacketLength > pContext->networkBuffer.size )
        {
            LogError( ( "Incoming packet size is bigger than MQTT buffer size. Total packet length %" PRIu32,
                        totalMQTTPacketLength ) );
            status = MQTTRecvFailed;
        }
        /* If the total packet is of more length than the bytes we have available. */
        else if( totalMQTTPacketLength > pContext->index )
        {
            status = MQTTNeedMoreBytes;
        }
        else
        {
            /* MISRA else. */
        }

        /* Handle received packet. If incomplete data was read then this will not execute. */
        if( status == MQTTSuccess )
        {
            incomingPacket.pRemainingData = &pContext->networkBuffer.pBuffer[ incomingPacket.headerLength ];

            /* PUBLISH packets allow flags in the lower four bits. For other
             * packet types, they are reserved. */
            if( ( incomingPacket.type & 0xF0U ) == MQTT_PACKET_TYPE_PUBLISH )
            {
                status = handleIncomingPublish( pContext, &incomingPacket );
            }
            else if( incomingPacket.type == MQTT_PACKET_TYPE_DISCONNECT )
            {
                status = handleIncomingDisconnect( pContext, &incomingPacket );

                if( status == MQTTSuccess )
                {
                    LogInfo( ( "Disconnected from the broker." ) );
                }
                else if( status != MQTTEventCallbackFailed )
                {
                    /* Incoming packet is malformed at this stage. */
                    MQTTSuccessFailReasonCode_t reason = MQTT_REASON_DISCONNECT_MALFORMED_PACKET;
                    status = MQTT_Disconnect( pContext, NULL, &reason );

                    if( status != MQTTSuccess )
                    {
                        LogError( ( "Failed to send disconnect following a malformed disconnect "
                                    "from the server. coreMQTT will forcefully disconnect now." ) );
                    }
                    else
                    {
                        status = MQTTStatusNotConnected;
                    }
                }
                else /* At this point the callback has failed. */
                {
                    /* TODO: If handling fails, the packet should be
                     * resent to the application or not? */
                }

                MQTT_PRE_STATE_UPDATE_HOOK( pContext );
                pContext->connectStatus = MQTTNotConnected;
                MQTT_POST_STATE_UPDATE_HOOK( pContext );
            }
            else
            {
                status = handleIncomingAck( pContext, &incomingPacket, manageKeepAlive );

                /* TODO: decide what to do when the app callback has failed.
                 * Should the packet be re-sent to the app? */
            }

            if( status == MQTTSuccess )
            {
                /* Update the index to reflect the remaining bytes in the buffer.  */
                pContext->index -= totalMQTTPacketLength;

                /* Move the remaining bytes to the front of the buffer. */
                ( void ) memmove( pContext->networkBuffer.pBuffer,
                                  &( pContext->networkBuffer.pBuffer[ totalMQTTPacketLength ] ),
                                  pContext->index );

                pContext->lastPacketRxTime = pContext->getTime();
            }
        }
    } while( ( pContext->index > 0U ) && ( status == MQTTSuccess ) );

    if( status == MQTTNoDataAvailable )
    {
        /* No data available is not an error. Reset to MQTTSuccess so the
         * return code will indicate success. */
        status = MQTTSuccess;
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t validateSubscribeUnsubscribeParams( const MQTTContext_t * pContext,
                                                        const MQTTSubscribeInfo_t * pSubscriptionList,
                                                        size_t subscriptionCount,
                                                        uint16_t packetId,
                                                        MQTTSubscriptionType_t subscriptionType )
{
    MQTTStatus_t status = MQTTSuccess;
    size_t iterator;

    /* Validate all the parameters. */
    if( ( pContext == NULL ) || ( pSubscriptionList == NULL ) )
    {
        LogError( ( "Argument cannot be NULL: pContext=%p, "
                    "pSubscriptionList=%p.",
                    ( const void * ) pContext,
                    ( const void * ) pSubscriptionList ) );
        status = MQTTBadParameter;
    }
    else if( subscriptionCount == 0UL )
    {
        LogError( ( "Subscription count is 0." ) );
        status = MQTTBadParameter;
    }
    else if( packetId == 0U )
    {
        LogError( ( "Packet Id for subscription packet is 0." ) );
        status = MQTTBadParameter;
    }
    else
    {
        if( pContext->incomingPublishRecords == NULL )
        {
            for( iterator = 0U; iterator < subscriptionCount; iterator++ )
            {
                if( pSubscriptionList[ iterator ].qos > MQTTQoS0 )
                {
                    LogError( ( "The incoming publish record list is not "
                                "initialised for QoS1/QoS2 records. Please call "
                                "MQTT_InitStatefulQoS to enable use of QoS1 and "
                                "QoS2 packets." ) );
                    status = MQTTBadParameter;
                    break;
                }
            }
        }

        if( status == MQTTSuccess )
        {
            for( iterator = 0U; iterator < subscriptionCount; iterator++ )
            {
                status = validateTopicFilter( pContext, pSubscriptionList, iterator, subscriptionType );
            }
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static size_t addEncodedStringToVector( uint8_t serializedLength[ CORE_MQTT_SERIALIZED_LENGTH_FIELD_BYTES ],
                                        const char * const string,
                                        uint16_t length,
                                        TransportOutVector_t * iterator,
                                        uint32_t * updatedLength )
{
    uint32_t packetLength = 0U;
    TransportOutVector_t * pLocalIterator = iterator;
    size_t vectorsAdded = 0U;

    /* When length is non-zero, the string must be non-NULL. */
    assert( ( length != 0U ) ? ( string != NULL ) : true );

    serializedLength[ 0 ] = ( ( uint8_t ) ( ( length ) >> 8 ) );
    serializedLength[ 1 ] = ( ( uint8_t ) ( ( length ) & 0x00ffU ) );

    /* Add the serialized length of the string first. */
    pLocalIterator[ 0 ].iov_base = serializedLength;
    pLocalIterator[ 0 ].iov_len = CORE_MQTT_SERIALIZED_LENGTH_FIELD_BYTES;
    vectorsAdded++;
    packetLength = CORE_MQTT_SERIALIZED_LENGTH_FIELD_BYTES;

    /* Sometimes the string can be NULL that is, of 0 length. In that case,
     * only the length field should be encoded in the vector. */
    if( ( string != NULL ) && ( length != 0U ) )
    {
        /* Then add the pointer to the string itself. */
        pLocalIterator[ 1 ].iov_base = string;
        pLocalIterator[ 1 ].iov_len = length;
        vectorsAdded++;
        packetLength += length;
    }

    ( *updatedLength ) = ( *updatedLength ) + packetLength;

    return vectorsAdded;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t sendSubscribeWithoutCopy( MQTTContext_t * pContext,
                                              const MQTTSubscribeInfo_t * pSubscriptionList,
                                              size_t subscriptionCount,
                                              uint16_t packetId,
                                              uint32_t remainingLength,
                                              const MQTTPropBuilder_t * pPropertyBuilder )
{
    MQTTStatus_t status = MQTTSuccess;
    uint8_t * pIndex;

    /**
     * Fixed Size Properties
     */
    TransportOutVector_t pIoVector[ MQTT_SUB_UNSUB_MAX_VECTORS ];
    TransportOutVector_t * pIterator;
    uint8_t serializedTopicFieldLength[ MQTT_SUB_UNSUB_MAX_VECTORS ][ CORE_MQTT_SERIALIZED_LENGTH_FIELD_BYTES ];
    uint8_t subscriptionOptionsArray[ MQTT_SUB_UNSUB_MAX_VECTORS / CORE_MQTT_SUBSCRIBE_PER_TOPIC_VECTOR_LENGTH ];
    uint32_t totalPacketLength = 0U;
    size_t ioVectorLength = 0U;
    size_t subscriptionsSent = 0U;
    size_t vectorsAdded = 0U;
    size_t topicFieldLengthIndex;
    uint32_t subscribePropLen = 0;
    size_t currentOptionIndex = 0U;

    /**
     * Maximum number of bytes by the fixed header of a SUBSCRIBE packet.
     * MQTT Control Byte 0 + 1 = 1
     * Remaining Length    + 4 = 5
     * Packet Id           + 2 = 7
     */
    uint8_t subscribeHeader[ 7U ];

    /**
     * Maximum number of bytes to send the Property Length.
     * Property Length  0 + 4 = 4
     */
    uint8_t propertyLength[ 4U ];

    assert( pContext != NULL );
    assert( pSubscriptionList != NULL );

    pIndex = subscribeHeader;
    pIterator = pIoVector;

    pIndex = serializeSubscribeHeader( remainingLength, pIndex, packetId );
    assert( ( pIndex - subscribeHeader ) <= 7 );

    pIterator->iov_base = subscribeHeader;
    /* More details at: https://github.com/FreeRTOS/coreMQTT/blob/main/MISRA.md#rule-182 */
    /* More details at: https://github.com/FreeRTOS/coreMQTT/blob/main/MISRA.md#rule-108 */
    /* coverity[misra_c_2012_rule_18_2_violation] */
    /* coverity[misra_c_2012_rule_10_8_violation] */
    pIterator->iov_len = ( size_t ) ( pIndex - subscribeHeader );

    /* The length will be a value between 0 and 7. No need to check for overflow. */
    totalPacketLength += ( uint32_t ) pIterator->iov_len;
    pIterator++;
    ioVectorLength++;

    /**
     * Sending Property Buffer
     */
    if( ( pPropertyBuilder != NULL ) && ( pPropertyBuilder->pBuffer != NULL ) )
    {
        assert( !CHECK_SIZE_T_OVERFLOWS_32BIT( pPropertyBuilder->currentIndex ) &&
                ( pPropertyBuilder->currentIndex < MQTT_REMAINING_LENGTH_INVALID ) );
        subscribePropLen = ( uint32_t ) pPropertyBuilder->currentIndex;
    }

    pIndex = encodeVariableLength( propertyLength, subscribePropLen );
    pIterator->iov_base = propertyLength;
    /* More details at: https://github.com/FreeRTOS/coreMQTT/blob/main/MISRA.md#rule-182 */
    /* More details at: https://github.com/FreeRTOS/coreMQTT/blob/main/MISRA.md#rule-108 */
    /* coverity[misra_c_2012_rule_18_2_violation] */
    /* coverity[misra_c_2012_rule_10_8_violation] */
    pIterator->iov_len = ( size_t ) ( pIndex - propertyLength );
    totalPacketLength += ( uint32_t ) pIterator->iov_len;
    pIterator++;
    ioVectorLength++;

    if( subscribePropLen > 0U )
    {
        pIterator->iov_base = pPropertyBuilder->pBuffer;
        pIterator->iov_len = pPropertyBuilder->currentIndex;

        if( ADDITION_WILL_OVERFLOW_U32( totalPacketLength, ( uint32_t ) pIterator->iov_len ) )
        {
            LogError( ( "MQTT packet size must be less than 268435461. Adding properties will overflow the limit." ) );
            status = MQTTBadParameter;
        }
        else
        {
            totalPacketLength += ( uint32_t ) pIterator->iov_len;
            pIterator++;
            ioVectorLength++;
        }
    }

    while( ( status == MQTTSuccess ) && ( subscriptionsSent < subscriptionCount ) )
    {
        /* Reset the index for next iteration. */
        topicFieldLengthIndex = 0;

        /* Check whether the subscription topic (with QoS) will fit in the
         * given vector. */
        while( ( ioVectorLength <= ( MQTT_SUB_UNSUB_MAX_VECTORS - CORE_MQTT_SUBSCRIBE_PER_TOPIC_VECTOR_LENGTH ) ) &&
               ( subscriptionsSent < subscriptionCount ) )
        {
            if( ADDITION_WILL_OVERFLOW_U32( totalPacketLength, 2U ) ||
                /* We can cast topic filter to 32-bits as we have verified that this will not overflow 16-bit value too. */
                ADDITION_WILL_OVERFLOW_U32( totalPacketLength + 2U, ( ( uint32_t ) pSubscriptionList[ subscriptionsSent ].topicFilterLength ) ) ||
                ( ( totalPacketLength + 2U + ( uint32_t ) pSubscriptionList[ subscriptionsSent ].topicFilterLength ) > MQTT_MAX_PACKET_SIZE ) )
            {
                LogError( ( "Total MQTT packet size must be less than 268435461" ) );
                status = MQTTBadParameter;
            }
            else if( CHECK_SIZE_T_OVERFLOWS_16BIT( pSubscriptionList[ subscriptionsSent ].topicFilterLength ) )
            {
                LogError( ( "Topic filter length cannot be bigger than 65535." ) );
                status = MQTTBadParameter;
            }
            else
            {
                /* All values are correct. */
            }

            if( status != MQTTSuccess )
            {
                break;
            }

            /* The topic filter and the filter length gets sent next. (filter length - 2 bytes , topic filter - utf - 8 ) */
            vectorsAdded = addEncodedStringToVector( serializedTopicFieldLength[ topicFieldLengthIndex ],
                                                     pSubscriptionList[ subscriptionsSent ].pTopicFilter,
                                                     ( uint16_t ) pSubscriptionList[ subscriptionsSent ].topicFilterLength,
                                                     pIterator,
                                                     &totalPacketLength );

            /* Update the pointer after the above operation. */
            pIterator = &pIterator[ vectorsAdded ];
            ioVectorLength += vectorsAdded;

            /* Lastly, send the subscription options. */
            addSubscriptionOptions( pSubscriptionList[ subscriptionsSent ],
                                    subscriptionOptionsArray,
                                    currentOptionIndex );

            pIterator->iov_base = &( subscriptionOptionsArray[ currentOptionIndex ] );
            pIterator->iov_len = 1U;
            totalPacketLength += 1U;
            pIterator++;
            ioVectorLength++;
            currentOptionIndex++;

            subscriptionsSent++;
            topicFieldLengthIndex++;
        }

        if( ( status == MQTTSuccess ) && ( totalPacketLength > MQTT_MAX_PACKET_SIZE ) )
        {
            LogError( ( "Total MQTT packet size must be less than 268435461" ) );
            status = MQTTBadParameter;
        }

        if( status == MQTTSuccess )
        {
            if( sendMessageVector( pContext, pIoVector, ioVectorLength ) != ( int32_t ) totalPacketLength )
            {
                LogError( ( "Error in sending SUBSCRIBE packet" ) );
                status = MQTTSendFailed;
            }

            /* Update the iterator for the next potential loop iteration. */
            pIterator = pIoVector;

            /* Reset the vector length for the next potential loop iteration. */
            ioVectorLength = 0U;
            /* Reset the packet length for the next potential loop iteration. */
            totalPacketLength = 0U;
            /* Reset index of the subscriptionOptionsArray for the next potential loop iteration. */
            currentOptionIndex = 0U;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t sendUnsubscribeWithoutCopy( MQTTContext_t * pContext,
                                                const MQTTSubscribeInfo_t * pSubscriptionList,
                                                size_t subscriptionCount,
                                                uint16_t packetId,
                                                uint32_t remainingLength,
                                                const MQTTPropBuilder_t * pPropertyBuilder )
{
    MQTTStatus_t status = MQTTSuccess;
    uint8_t * pIndex;

    /**
     * Fixed Size Properties
     */
    TransportOutVector_t pIoVector[ MQTT_SUB_UNSUB_MAX_VECTORS ];
    TransportOutVector_t * pIterator;
    uint8_t serializedTopicFieldLength[ MQTT_SUB_UNSUB_MAX_VECTORS ][ CORE_MQTT_SERIALIZED_LENGTH_FIELD_BYTES ];
    uint32_t totalPacketLength = 0U;
    size_t ioVectorLength = 0U;
    size_t unsubscriptionsSent = 0U;
    size_t vectorsAdded = 0U;
    size_t topicFieldLengthIndex;
    uint32_t unsubscribePropLen = 0U;

    /**
     * Maximum number of bytes by the fixed header of a SUBSCRIBE packet.
     * MQTT Control Byte 0 + 1 = 1
     * Remaining Length    + 4 = 5
     * Packet Id           + 2 = 7
     */
    uint8_t unsubscribeHeader[ 7U ];

    /**
     * Maximum number of bytes to send the Property Length.
     * Property Length  0 + 4 = 4
     */
    uint8_t propertyLength[ 4U ];

    pIndex = unsubscribeHeader;
    pIterator = pIoVector;

    pIndex = serializeUnsubscribeHeader( remainingLength, pIndex, packetId );

    pIterator->iov_base = unsubscribeHeader;
    /* More details at: https://github.com/FreeRTOS/coreMQTT/blob/main/MISRA.md#rule-182 */
    /* More details at: https://github.com/FreeRTOS/coreMQTT/blob/main/MISRA.md#rule-108 */
    /* coverity[misra_c_2012_rule_18_2_violation] */
    /* coverity[misra_c_2012_rule_10_8_violation] */
    pIterator->iov_len = ( size_t ) ( pIndex - unsubscribeHeader );
    assert( pIterator->iov_len <= 7 );

    totalPacketLength += ( uint32_t ) pIterator->iov_len;
    pIterator++;
    ioVectorLength++;

    /**
     * Sending Property Buffer
     */
    if( ( pPropertyBuilder != NULL ) && ( pPropertyBuilder->pBuffer != NULL ) )
    {
        assert( !CHECK_SIZE_T_OVERFLOWS_32BIT( pPropertyBuilder->currentIndex ) );
        unsubscribePropLen = ( uint32_t ) pPropertyBuilder->currentIndex;
    }

    pIndex = encodeVariableLength( propertyLength, unsubscribePropLen );
    pIterator->iov_base = propertyLength;
    /* More details at: https://github.com/FreeRTOS/coreMQTT/blob/main/MISRA.md#rule-182 */
    /* More details at: https://github.com/FreeRTOS/coreMQTT/blob/main/MISRA.md#rule-108 */
    /* coverity[misra_c_2012_rule_18_2_violation] */
    /* coverity[misra_c_2012_rule_10_8_violation] */
    pIterator->iov_len = ( size_t ) ( pIndex - propertyLength );
    totalPacketLength += ( uint32_t ) pIterator->iov_len;
    pIterator++;
    ioVectorLength++;

    if( unsubscribePropLen > 0U )
    {
        pIterator->iov_base = pPropertyBuilder->pBuffer;
        pIterator->iov_len = pPropertyBuilder->currentIndex;

        if( CHECK_SIZE_T_OVERFLOWS_32BIT( pIterator->iov_len ) ||
            ADDITION_WILL_OVERFLOW_U32( totalPacketLength, ( uint32_t ) pIterator->iov_len ) ||
            ( ( totalPacketLength + pIterator->iov_len ) > MQTT_MAX_REMAINING_LENGTH ) )
        {
            LogError( ( "Total packet length must less than 268435461." ) );
            status = MQTTBadParameter;
        }
        else
        {
            totalPacketLength += ( uint32_t ) pIterator->iov_len;
            pIterator++;
            ioVectorLength++;
        }
    }

    while( ( status == MQTTSuccess ) && ( unsubscriptionsSent < subscriptionCount ) )
    {
        /* Reset the index for next iteration. */
        topicFieldLengthIndex = 0;

        /* Check whether the subscription topic (with QoS) will fit in the
         * given vector. */
        while( ( ioVectorLength <= ( MQTT_SUB_UNSUB_MAX_VECTORS - CORE_MQTT_UNSUBSCRIBE_PER_TOPIC_VECTOR_LENGTH ) ) &&
               ( unsubscriptionsSent < subscriptionCount ) )
        {
            if( ADDITION_WILL_OVERFLOW_U32( totalPacketLength, 2U ) ||
                ADDITION_WILL_OVERFLOW_U32( totalPacketLength + 2U, ( uint32_t ) pSubscriptionList[ unsubscriptionsSent ].topicFilterLength ) ||
                ( ( totalPacketLength + 2U + ( uint32_t ) pSubscriptionList[ unsubscriptionsSent ].topicFilterLength ) > MQTT_MAX_PACKET_SIZE ) )
            {
                LogError( ( "Total MQTT packet size must be less than 268435461" ) );
                status = MQTTBadParameter;
                break;
            }

            /* The topic filter and the filter length gets sent next. (filter length - 2 bytes , topic filter - utf8 ) */
            vectorsAdded = addEncodedStringToVector( serializedTopicFieldLength[ topicFieldLengthIndex ],
                                                     pSubscriptionList[ unsubscriptionsSent ].pTopicFilter,
                                                     ( uint16_t ) pSubscriptionList[ unsubscriptionsSent ].topicFilterLength,
                                                     pIterator,
                                                     &totalPacketLength );

            /* Update the pointer after the above operation. */
            pIterator = &pIterator[ vectorsAdded ];
            /* Update the total count based on how many vectors were added. */
            ioVectorLength += vectorsAdded;

            unsubscriptionsSent++;

            /* Update the index for next iteration. */
            topicFieldLengthIndex++;
        }

        if( totalPacketLength > MQTT_MAX_PACKET_SIZE )
        {
            LogError( ( "Total MQTT packet size must be less than 268435461." ) );
            status = MQTTBadParameter;
        }

        if( status == MQTTSuccess )
        {
            if( sendMessageVector( pContext, pIoVector, ioVectorLength ) != ( int32_t ) totalPacketLength )
            {
                LogError( ( "Error in sending UNSUBSCRIBE packet" ) );
                status = MQTTSendFailed;
            }

            /* Update the iterator for the next potential loop iteration. */
            pIterator = pIoVector;
            /* Reset the vector length for the next potential loop iteration. */
            ioVectorLength = 0U;
            /* Reset the packet length for the next potential loop iteration. */
            totalPacketLength = 0U;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t sendPublishWithoutCopy( MQTTContext_t * pContext,
                                            const MQTTPublishInfo_t * pPublishInfo,
                                            uint8_t * pMqttHeader,
                                            size_t headerSize,
                                            uint16_t packetId,
                                            const MQTTPropBuilder_t * pPropertyBuilder )
{
    MQTTStatus_t status = MQTTSuccess;
    size_t ioVectorLength;
    uint32_t totalMessageLength;
    uint32_t publishPropLength = 0U;
    bool dupFlagChanged = false;

    /* Bytes required to encode the packet ID in an MQTT header according to
     * the MQTT specification. */
    uint8_t serializedPacketID[ 2U ];

    /**
     * Maximum number of bytes to send the Property Length.
     * Property Length  0 + 4 = 4
     */
    uint8_t propertyLength[ 4U ];

    /* Maximum number of vectors required to encode and send a publish
     * packet. The breakdown is shown below.
     * Fixed header (including topic string length)      0 + 1 = 1
     * Topic string                                        + 1 = 2
     * Packet ID (only when QoS > QoS0)                    + 1 = 3
     * Property Length                                     + 1 = 4
     * Optional Properties                                 + 1 = 5
     * Payload                                             + 1 = 6  */

    TransportOutVector_t pIoVector[ 6U ];
    uint8_t * pIndex;
    TransportOutVector_t * iterator;

    assert( pContext != NULL );
    assert( pPublishInfo != NULL );
    assert( !CHECK_SIZE_T_OVERFLOWS_16BIT( pPublishInfo->topicNameLength ) );
    assert( !CHECK_SIZE_T_OVERFLOWS_32BIT( pPublishInfo->payloadLength ) );
    assert( headerSize <= 7U );

    /* The header is sent first. */
    pIoVector[ 0U ].iov_base = pMqttHeader;
    pIoVector[ 0U ].iov_len = headerSize;
    totalMessageLength = ( uint32_t ) headerSize;

    /* Then the topic name has to be sent. */
    pIoVector[ 1U ].iov_base = pPublishInfo->pTopicName;
    pIoVector[ 1U ].iov_len = pPublishInfo->topicNameLength;
    totalMessageLength += ( uint32_t ) pPublishInfo->topicNameLength;

    /* The next field's index should be 2 as the first two fields
     * have been filled in. */
    ioVectorLength = 2U;

    if( pPublishInfo->qos > MQTTQoS0 )
    {
        /* Encode the packet ID. */
        serializedPacketID[ 0 ] = ( ( uint8_t ) ( ( packetId ) >> 8 ) );
        serializedPacketID[ 1 ] = ( ( uint8_t ) ( ( packetId ) & 0x00ffU ) );

        pIoVector[ ioVectorLength ].iov_base = serializedPacketID;
        pIoVector[ ioVectorLength ].iov_len = sizeof( serializedPacketID );

        ioVectorLength++;
        totalMessageLength += 2U;
    }

    if( ( pPropertyBuilder != NULL ) && ( pPropertyBuilder->pBuffer != NULL ) )
    {
        assert( !CHECK_SIZE_T_OVERFLOWS_32BIT( pPropertyBuilder->currentIndex ) );
        assert( pPropertyBuilder->currentIndex < MQTT_REMAINING_LENGTH_INVALID );

        publishPropLength = ( uint32_t ) pPropertyBuilder->currentIndex;
    }

    iterator = &pIoVector[ ioVectorLength ];
    pIndex = propertyLength;
    pIndex = encodeVariableLength( pIndex, publishPropLength );
    iterator->iov_base = propertyLength;
    /* More details at: https://github.com/FreeRTOS/coreMQTT/blob/main/MISRA.md#rule-182 */
    /* More details at: https://github.com/FreeRTOS/coreMQTT/blob/main/MISRA.md#rule-108 */
    /* coverity[misra_c_2012_rule_18_2_violation] */
    /* coverity[misra_c_2012_rule_10_8_violation] */
    iterator->iov_len = ( size_t ) ( pIndex - propertyLength );
    totalMessageLength += ( uint32_t ) iterator->iov_len;
    iterator++;
    ioVectorLength++;

    /* Serialize the publish properties, if provided. */
    if( publishPropLength > 0U )
    {
        iterator->iov_base = pPropertyBuilder->pBuffer;
        iterator->iov_len = pPropertyBuilder->currentIndex;

        if( CHECK_SIZE_T_OVERFLOWS_32BIT( pPropertyBuilder->currentIndex ) ||
            ADDITION_WILL_OVERFLOW_U32( totalMessageLength, pPropertyBuilder->currentIndex ) ||
            ( ( totalMessageLength + pPropertyBuilder->currentIndex ) > MQTT_MAX_PACKET_SIZE ) )
        {
            LogError( ( "Total MQTT packet size must be less than 268435461." ) );
            status = MQTTBadParameter;
        }
        else
        {
            totalMessageLength += ( uint32_t ) iterator->iov_len;
            iterator++;
            ioVectorLength++;
        }
    }

    /* Publish packets are allowed to contain no payload. */
    if( ( status == MQTTSuccess ) && ( pPublishInfo->payloadLength > 0U ) )
    {
        pIoVector[ ioVectorLength ].iov_base = pPublishInfo->pPayload;
        pIoVector[ ioVectorLength ].iov_len = pPublishInfo->payloadLength;

        if( ADDITION_WILL_OVERFLOW_U32( totalMessageLength, pPublishInfo->payloadLength ) ||
            ( ( totalMessageLength + pPublishInfo->payloadLength ) > MQTT_MAX_PACKET_SIZE ) )
        {
            LogError( ( "Total MQTT packet size must be less than 268435461." ) );
            status = MQTTBadParameter;
        }
        else
        {
            ioVectorLength++;
            totalMessageLength += ( uint32_t ) pPublishInfo->payloadLength;
        }
    }

    /* Store a copy of the publish for retransmission purposes. */
    if( ( status == MQTTSuccess ) &&
        ( pPublishInfo->qos > MQTTQoS0 ) &&
        ( pContext->storeFunction != NULL ) )
    {
        /* If not already set, set the dup flag before storing a copy of the publish
         * this is because on retrieving back this copy we will get it in the form of an
         * array of TransportOutVector_t that holds the data in a const pointer which cannot be
         * changed after retrieving. */
        if( pPublishInfo->dup != true )
        {
            status = MQTT_UpdateDuplicatePublishFlag( pMqttHeader, true );

            dupFlagChanged = ( status == MQTTSuccess );
        }

        if( status == MQTTSuccess )
        {
            MQTTVec_t mqttVec;

            mqttVec.pVector = pIoVector;
            mqttVec.vectorLen = ioVectorLength;

            if( pContext->storeFunction( pContext, ( uint32_t ) packetId, &mqttVec ) != true )
            {
                status = MQTTPublishStoreFailed;
            }
        }

        /* change the value of the dup flag to its original, if it was changed */
        if( ( status == MQTTSuccess ) && ( dupFlagChanged == true ) )
        {
            status = MQTT_UpdateDuplicatePublishFlag( pMqttHeader, false );
        }
    }

    if( ( status == MQTTSuccess ) &&
        ( sendMessageVector( pContext, pIoVector, ioVectorLength ) != ( int32_t ) totalMessageLength ) )
    {
        status = MQTTSendFailed;
    }

    return status;
}

/*-----------------------------------------------------------*/

/**
 * @brief Tracks the state of building a scatter-gather IO vector list.
 *
 * Groups the iterator, vector count, and accumulated message length
 * that are always passed together when appending to an IO vector.
 */
typedef struct IoVecState
{
    TransportOutVector_t * pIterator; /**< Current position in the IO vector array. */
    size_t ioVectorLength;            /**< Number of vectors added so far. */
    uint32_t totalMessageLength;      /**< Accumulated byte count across all vectors. */
} IoVecState_t;

/**
 * @brief Add an encoded string to the IO vector if it fits within maxPacketSize.
 * Returns MQTTBadParameter if the addition would overflow.
 */
static MQTTStatus_t addStringToVectorChecked( uint8_t * pLenBuf,
                                              const char * pStr,
                                              uint16_t strLen,
                                              IoVecState_t * pVecState )
{
    MQTTStatus_t status = MQTTSuccess;

    if( ADDITION_WILL_OVERFLOW_U32( pVecState->totalMessageLength, 2U ) ||
        ADDITION_WILL_OVERFLOW_U32( pVecState->totalMessageLength + 2U, ( uint32_t ) strLen ) ||
        ( ( pVecState->totalMessageLength + 2U + ( uint32_t ) strLen ) > MQTT_MAX_PACKET_SIZE ) )
    {
        LogError( ( "Total MQTT packet size must be less than 268435461" ) );
        status = MQTTBadParameter;
    }
    else
    {
        size_t vectorsAdded = addEncodedStringToVector( pLenBuf, pStr, strLen,
                                                        pVecState->pIterator,
                                                        &pVecState->totalMessageLength );
        pVecState->pIterator = &( pVecState->pIterator[ vectorsAdded ] );
        pVecState->ioVectorLength += vectorsAdded;
    }

    return status;
}

/**
 * @brief Append will properties, topic, and payload vectors to the IO vector.
 */
static MQTTStatus_t appendWillVectors( const MQTTPublishInfo_t * pWillInfo,
                                       const MQTTPropBuilder_t * pWillPropertyBuilder,
                                       IoVecState_t * pVecState,
                                       uint8_t * pWillPropertyLength,
                                       uint8_t * pSerializedTopicLength,
                                       uint8_t * pSerializedPayloadLength )
{
    MQTTStatus_t status = MQTTSuccess;
    uint32_t willPropsLen = 0U;

    if( ( pWillPropertyBuilder != NULL ) && ( pWillPropertyBuilder->pBuffer != NULL ) )
    {
        willPropsLen = ( uint32_t ) pWillPropertyBuilder->currentIndex;
    }

    pVecState->pIterator->iov_base = pWillPropertyLength;
    /* coverity[misra_c_2012_rule_18_2_violation] */
    /* coverity[misra_c_2012_rule_10_8_violation] */
    pVecState->pIterator->iov_len = ( size_t ) ( encodeVariableLength( pWillPropertyLength, willPropsLen ) - pWillPropertyLength );

    if( ADDITION_WILL_OVERFLOW_U32( pVecState->totalMessageLength, pVecState->pIterator->iov_len ) ||
        ( ( pVecState->totalMessageLength + pVecState->pIterator->iov_len ) > MQTT_MAX_PACKET_SIZE ) )
    {
        LogError( ( "Total MQTT packet size must be less than 268435461" ) );
        status = MQTTBadParameter;
    }
    else
    {
        pVecState->totalMessageLength += ( uint32_t ) pVecState->pIterator->iov_len;
        pVecState->pIterator++;
        pVecState->ioVectorLength++;
    }

    if( ( status == MQTTSuccess ) && ( willPropsLen > 0U ) )
    {
        assert( !CHECK_SIZE_T_OVERFLOWS_32BIT( pWillPropertyBuilder->currentIndex ) );
        pVecState->pIterator->iov_base = pWillPropertyBuilder->pBuffer;
        pVecState->pIterator->iov_len = pWillPropertyBuilder->currentIndex;

        if( ADDITION_WILL_OVERFLOW_U32( pVecState->totalMessageLength, pVecState->pIterator->iov_len ) ||
            ( ( pVecState->totalMessageLength + pVecState->pIterator->iov_len ) > MQTT_MAX_PACKET_SIZE ) )
        {
            LogError( ( "Total MQTT packet size must be less than 268435461" ) );
            status = MQTTBadParameter;
        }
        else
        {
            pVecState->totalMessageLength += ( uint32_t ) pVecState->pIterator->iov_len;
            pVecState->pIterator++;
            pVecState->ioVectorLength++;
        }
    }

    if( status == MQTTSuccess )
    {
        status = addStringToVectorChecked( pSerializedTopicLength,
                                           pWillInfo->pTopicName,
                                           ( uint16_t ) pWillInfo->topicNameLength,
                                           pVecState );

        if( status == MQTTSuccess )
        {
            status = addStringToVectorChecked( pSerializedPayloadLength,
                                               pWillInfo->pPayload,
                                               ( uint16_t ) pWillInfo->payloadLength,
                                               pVecState );
        }
    }

    return status;
}

static MQTTStatus_t sendConnectWithoutCopy( MQTTContext_t * pContext,
                                            const MQTTConnectInfo_t * pConnectInfo,
                                            const MQTTPublishInfo_t * pWillInfo,
                                            uint32_t remainingLength,
                                            const MQTTPropBuilder_t * pPropertyBuilder,
                                            const MQTTPropBuilder_t * pWillPropertyBuilder )
{
    MQTTStatus_t status = MQTTSuccess;
    IoVecState_t vecState;
    uint32_t connectPropLen = 0U;
    int32_t bytesSentOrError;
    uint8_t * pIndex;
    uint8_t serializedClientIDLength[ 2U ];
    uint8_t serializedUsernameLength[ 2U ];
    uint8_t serializedPasswordLength[ 2U ];
    uint8_t serializedWillTopicLength[ 2U ];
    uint8_t serializedWillPayloadLength[ 2U ];

    /**
     * Maximum number of bytes to send the Property Length.
     * Property Length  0 + 4 = 4
     */
    uint8_t propertyLength[ 4U ];
    uint8_t willPropertyLength[ 4U ];

    /* Maximum number of bytes required by the fixed part of the CONNECT
     * packet header according to the MQTT specification.
     * MQTT Control Byte          0 + 1 = 1
     * Remaining length (max)       + 4 = 5
     * Protocol Name Length         + 2 = 7
     * Protocol Name (MQTT)         + 4 = 11
     * Protocol level               + 1 = 12
     * Connect flags                + 1 = 13
     * Keep alive                   + 2 = 15
     */

    uint8_t connectPacketHeader[ 15U ];

    /* The maximum vectors required to encode and send a connect packet. The
     * breakdown is shown below.
     * Fixed header      0 + 1 = 1
     * Connect Properties  + 2 = 3
     * Client ID           + 2 = 5
     * Will Properties     + 2 = 7
     * Will topic          + 2 = 9
     * Will payload        + 2 = 11
     * Username            + 2 = 13
     * Password            + 2 = 15
     */
    TransportOutVector_t pIoVector[ 15U ];

    assert( !CHECK_SIZE_T_OVERFLOWS_16BIT( pConnectInfo->clientIdentifierLength ) );

    if( pWillInfo != NULL )
    {
        assert( !CHECK_SIZE_T_OVERFLOWS_16BIT( pWillInfo->topicNameLength ) );
    }

    vecState.pIterator = pIoVector;
    vecState.ioVectorLength = 0U;
    vecState.totalMessageLength = 0U;
    pIndex = connectPacketHeader;

    /* Validate arguments. */
    if( ( pWillInfo != NULL ) && ( pWillInfo->pTopicName == NULL ) )
    {
        LogError( ( "pWillInfo->pTopicName cannot be NULL if Will is present." ) );
        status = MQTTBadParameter;
    }
    else
    {
        pIndex = serializeConnectFixedHeader( pIndex, pConnectInfo, pWillInfo, remainingLength );

        /* Set serverKeepAlive; may be overwritten by CONNACK. */
        pContext->connectionProperties.serverKeepAlive = pConnectInfo->keepAliveSeconds;

        vecState.pIterator->iov_base = connectPacketHeader;
        /* coverity[misra_c_2012_rule_18_2_violation] */
        /* coverity[misra_c_2012_rule_10_8_violation] */
        vecState.pIterator->iov_len = ( size_t ) ( pIndex - connectPacketHeader );
        vecState.totalMessageLength += ( uint32_t ) vecState.pIterator->iov_len;
        vecState.pIterator++;
        vecState.ioVectorLength++;

        if( ( pPropertyBuilder != NULL ) && ( pPropertyBuilder->pBuffer != NULL ) )
        {
            assert( !CHECK_SIZE_T_OVERFLOWS_32BIT( pPropertyBuilder->currentIndex ) );
            assert( pPropertyBuilder->currentIndex < MQTT_REMAINING_LENGTH_INVALID );
            connectPropLen = ( uint32_t ) pPropertyBuilder->currentIndex;
        }

        pIndex = encodeVariableLength( propertyLength, connectPropLen );
        vecState.pIterator->iov_base = propertyLength;
        /* coverity[misra_c_2012_rule_18_2_violation] */
        /* coverity[misra_c_2012_rule_10_8_violation] */
        vecState.pIterator->iov_len = ( size_t ) ( pIndex - propertyLength );
        vecState.totalMessageLength += ( uint32_t ) vecState.pIterator->iov_len;
        vecState.pIterator++;
        vecState.ioVectorLength++;

        /* Serialize CONNECT properties, if present. */
        if( connectPropLen > 0U )
        {
            vecState.pIterator->iov_base = pPropertyBuilder->pBuffer;
            vecState.pIterator->iov_len = pPropertyBuilder->currentIndex;

            if( ADDITION_WILL_OVERFLOW_U32( vecState.totalMessageLength, vecState.pIterator->iov_len ) ||
                ( ( vecState.totalMessageLength + vecState.pIterator->iov_len ) > MQTT_MAX_PACKET_SIZE ) )
            {
                LogError( ( "Total MQTT packet size must be less than 268435461." ) );
                status = MQTTBadParameter;
            }
            else
            {
                vecState.totalMessageLength += ( uint32_t ) vecState.pIterator->iov_len;
                vecState.pIterator++;
                vecState.ioVectorLength++;
                status = updateContextWithConnectProps( pPropertyBuilder, &pContext->connectionProperties );
            }
        }

        /* Serialize client ID. */
        if( status == MQTTSuccess )
        {
            status = addStringToVectorChecked( serializedClientIDLength,
                                               pConnectInfo->pClientIdentifier,
                                               ( uint16_t ) pConnectInfo->clientIdentifierLength,
                                               &vecState );
        }

        /* Serialize will properties, topic, and payload. */
        if( ( status == MQTTSuccess ) && ( pWillInfo != NULL ) )
        {
            status = appendWillVectors( pWillInfo, pWillPropertyBuilder,
                                        &vecState, willPropertyLength,
                                        serializedWillTopicLength,
                                        serializedWillPayloadLength );
        }

        /* Serialize username. */
        if( ( status == MQTTSuccess ) && ( pConnectInfo->pUserName != NULL ) )
        {
            status = addStringToVectorChecked( serializedUsernameLength,
                                               pConnectInfo->pUserName,
                                               ( uint16_t ) pConnectInfo->userNameLength,
                                               &vecState );
        }

        /* Serialize password. */
        if( ( status == MQTTSuccess ) && ( pConnectInfo->pPassword != NULL ) )
        {
            status = addStringToVectorChecked( serializedPasswordLength,
                                               pConnectInfo->pPassword,
                                               ( uint16_t ) pConnectInfo->passwordLength,
                                               &vecState );
        }

        if( status == MQTTSuccess )
        {
            bytesSentOrError = sendMessageVector( pContext, pIoVector, vecState.ioVectorLength );

            if( bytesSentOrError != ( int32_t ) vecState.totalMessageLength )
            {
                status = MQTTSendFailed;
            }
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t receiveConnack( MQTTContext_t * pContext,
                                    uint32_t timeoutMs,
                                    bool cleanSession,
                                    MQTTPacketInfo_t * pIncomingPacket,
                                    bool * pSessionPresent )
{
    MQTTStatus_t status = MQTTSuccess;
    MQTTGetCurrentTimeFunc_t getTimeStamp = NULL;
    uint32_t entryTimeMs = 0U;
    bool breakFromLoop = false;
    uint16_t loopCount = 0U;
    MQTTDeserializedInfo_t deserializedInfo = { 0 };
    MQTTPropBuilder_t propBuffer = { 0 };

    assert( pContext != NULL );
    assert( pIncomingPacket != NULL );
    assert( pContext->getTime != NULL );

    getTimeStamp = pContext->getTime;

    /* Get the entry time for the function. */
    entryTimeMs = getTimeStamp();

    do
    {
        /* Transport read for incoming CONNACK packet type and length.
         * MQTT_GetIncomingPacketTypeAndLength is a blocking call and it is
         * returned after a transport receive timeout, an error, or a successful
         * receive of packet type and length. */
        status = MQTT_GetIncomingPacketTypeAndLength( pContext->transportInterface.recv,
                                                      pContext->transportInterface.pNetworkContext,
                                                      pIncomingPacket );

        /* The loop times out based on 2 conditions.
         * 1. If timeoutMs is greater than 0:
         *    Loop times out based on the timeout calculated by getTime()
         *    function.
         * 2. If timeoutMs is 0:
         *    Loop times out based on the maximum number of retries config
         *    MQTT_MAX_CONNACK_RECEIVE_RETRY_COUNT. This config will control
         *    maximum the number of retry attempts to read the CONNACK packet.
         *    A value of 0 for the config will try once to read CONNACK. */
        if( timeoutMs > 0U )
        {
            breakFromLoop = calculateElapsedTime( getTimeStamp(), entryTimeMs ) >= timeoutMs;
        }
        else
        {
            breakFromLoop = ( loopCount >= MQTT_MAX_CONNACK_RECEIVE_RETRY_COUNT );
            loopCount++;
        }

        /* Loop until there is data to read or if we have exceeded the timeout/retries. */
    } while( ( status == MQTTNoDataAvailable ) && ( breakFromLoop == false ) );

    if( status == MQTTSuccess )
    {
        /* Reading the remainder of the packet by transport recv.
         * Attempt to read once even if the timeout has expired.
         * Invoking receiveConnackPacket with remainingTime as 0 would attempt to
         * recv from network once. */
        if( pIncomingPacket->type == MQTT_PACKET_TYPE_CONNACK )
        {
            status = receiveConnackPacket( pContext,
                                           *pIncomingPacket );
        }
        /* TODO: Handle AUTH packets here as well. */
        else
        {
            LogError( ( "Incorrect packet type %X received while expecting"
                        " CONNACK(%X).",
                        ( unsigned int ) pIncomingPacket->type,
                        MQTT_PACKET_TYPE_CONNACK ) );
            status = MQTTBadResponse;
        }
    }

    if( status == MQTTSuccess )
    {
        /* Update the packet info pointer to the buffer read. */
        pIncomingPacket->pRemainingData = pContext->networkBuffer.pBuffer;

        /* Deserialize CONNACK. */
        status = MQTT_DeserializeConnAck( pIncomingPacket,
                                          pSessionPresent,
                                          &propBuffer,
                                          &pContext->connectionProperties );
    }

    /* If a clean session is requested, a session present should not be set by
     * broker. */
    if( status == MQTTSuccess )
    {
        if( ( cleanSession == true ) && ( *pSessionPresent == true ) )
        {
            LogError( ( "Unexpected session present flag in CONNACK response from broker."
                        " CONNECT request with clean session was made with broker." ) );
            status = MQTTBadResponse;
        }
    }

    if( status == MQTTSuccess )
    {
        LogDebug( ( "Received MQTT CONNACK successfully from broker." ) );
    }
    else
    {
        LogError( ( "CONNACK recv failed with status = %s.",
                    MQTT_Status_strerror( status ) ) );
    }

    if( ( status == MQTTSuccess ) || ( status == MQTTServerRefused ) )
    {
        deserializedInfo.deserializationResult = status;

        if( pContext->appCallback( pContext, pIncomingPacket, &deserializedInfo,
                                   NULL, NULL, &propBuffer ) == false )
        {
            status = MQTTEventCallbackFailed;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t handleUncleanSessionResumption( MQTTContext_t * pContext )
{
    MQTTStatus_t status = MQTTSuccess;
    MQTTStateCursor_t cursor = MQTT_STATE_CURSOR_INITIALIZER;
    uint16_t packetId = MQTT_PACKET_ID_INVALID;
    MQTTPublishState_t state = MQTTStateNull;
    size_t totalMessageLength = 0;
    uint8_t * pMqttPacket = NULL;

    assert( pContext != NULL );

    do
    {
        /* Get the next packet ID for which a PUBREL need to be resent. */
        packetId = MQTT_PubrelToResend( pContext, &cursor, &state );

        /* Resend all the PUBREL acks after session is reestablished. */
        if( packetId != MQTT_PACKET_ID_INVALID )
        {
            /* If we have the stored data, then we just need to send it. */
            if( pContext->retrieveFunction != NULL )
            {
                if( pContext->retrieveFunction( pContext, SET_INCOMING_PUB_FLAG( packetId ), &pMqttPacket, &totalMessageLength ) != true )
                {
                    LogError( ( "Failed to retrieve PUBREL with packet ID %u", packetId ) );
                    status = MQTTPublishRetrieveFailed;
                }
                else if( CHECK_SIZE_T_OVERFLOWS_32BIT( totalMessageLength ) ||
                         ( totalMessageLength > MQTT_MAX_PACKET_SIZE ) )
                {
                    LogError( ( "Total packet size returned by the retrieve function exceeds the MQTT Max packet size." ) );
                    status = MQTTBadParameter;
                }
                else
                {
                    MQTT_PRE_STATE_UPDATE_HOOK( pContext );

                    if( sendBuffer( pContext, pMqttPacket, totalMessageLength ) != ( int32_t ) totalMessageLength )
                    {
                        status = MQTTSendFailed;
                    }

                    MQTT_POST_STATE_UPDATE_HOOK( pContext );
                }
            }
            /* Otherwise, send default ACKs. */
            else
            {
                LogWarn( ( "No Application provided retransmission storage callbacks, sending 'default' PUBRECs." ) );
                status = sendPublishAcks( pContext, packetId, state );
            }
        }
    }
    while( ( packetId != MQTT_PACKET_ID_INVALID ) &&
           ( status == MQTTSuccess ) );

    if( ( status == MQTTSuccess ) &&
        ( pContext->retrieveFunction != NULL ) )
    {
        cursor = MQTT_STATE_CURSOR_INITIALIZER;

        /* Resend all the PUBLISH for which PUBACK/PUBREC is not received
         * after session is reestablished. */
        do
        {
            packetId = MQTT_PublishToResend( pContext, &cursor );

            if( packetId != MQTT_PACKET_ID_INVALID )
            {
                if( pContext->retrieveFunction( pContext, ( uint32_t ) packetId, &pMqttPacket, &totalMessageLength ) != true )
                {
                    LogError( ( "Failed to retrieve publish with packet ID %u", packetId ) );
                    status = MQTTPublishRetrieveFailed;
                }
                else if( CHECK_SIZE_T_OVERFLOWS_32BIT( totalMessageLength ) ||
                         ( totalMessageLength > MQTT_MAX_PACKET_SIZE ) )
                {
                    LogError( ( "Total packet size returned by the retrieve function exceeds the MQTT Max packet size." ) );
                    status = MQTTBadParameter;
                }
                else
                {
                    MQTT_PRE_STATE_UPDATE_HOOK( pContext );

                    if( sendBuffer( pContext, pMqttPacket, totalMessageLength ) != ( int32_t ) totalMessageLength )
                    {
                        status = MQTTSendFailed;
                    }

                    MQTT_POST_STATE_UPDATE_HOOK( pContext );
                }
            }
        } while( ( packetId != MQTT_PACKET_ID_INVALID ) &&
                 ( status == MQTTSuccess ) );
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t handleCleanSession( MQTTContext_t * pContext )
{
    MQTTStatus_t status = MQTTSuccess;
    MQTTStateCursor_t cursor = MQTT_STATE_CURSOR_INITIALIZER;
    uint16_t packetId = MQTT_PACKET_ID_INVALID;

    assert( pContext != NULL );

    /* Reset the index and clear the buffer when a new session is established. */
    pContext->index = 0;
    ( void ) memset( pContext->networkBuffer.pBuffer, 0, pContext->networkBuffer.size );

    if( pContext->outgoingPublishRecordMaxCount > 0U )
    {
        if( pContext->clearFunction != NULL )
        {
            cursor = MQTT_STATE_CURSOR_INITIALIZER;

            /* Clear the stored packets on clean session. */
            do
            {
                packetId = MQTT_PublishToResend( pContext, &cursor );

                if( packetId != MQTT_PACKET_ID_INVALID )
                {
                    pContext->clearFunction( pContext, ( uint32_t ) packetId );
                }
            } while( packetId != MQTT_PACKET_ID_INVALID );
        }

        /* Clear any existing records if a new session is established. */
        ( void ) memset( pContext->outgoingPublishRecords,
                         0x00,
                         pContext->outgoingPublishRecordMaxCount * sizeof( *pContext->outgoingPublishRecords ) );
    }

    if( pContext->incomingPublishRecordMaxCount > 0U )
    {
        if( pContext->clearFunction != NULL )
        {
            MQTTPublishState_t state;
            cursor = MQTT_STATE_CURSOR_INITIALIZER;

            /* Clear the stored PUBRELs on clean session. */
            do
            {
                state = MQTTStateNull;
                packetId = MQTT_PubrelToResend( pContext, &cursor, &state );

                if( packetId != MQTT_PACKET_ID_INVALID )
                {
                    pContext->clearFunction( pContext, SET_INCOMING_PUB_FLAG( packetId ) );
                }
            } while( packetId != MQTT_PACKET_ID_INVALID );
        }

        ( void ) memset( pContext->incomingPublishRecords,
                         0x00,
                         pContext->incomingPublishRecordMaxCount * sizeof( *pContext->incomingPublishRecords ) );
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t validatePublishParams( const MQTTContext_t * pContext,
                                           const MQTTPublishInfo_t * pPublishInfo,
                                           uint16_t packetId )
{
    MQTTStatus_t status = MQTTSuccess;

    /* Validate arguments. */
    if( ( pContext == NULL ) || ( pPublishInfo == NULL ) )
    {
        LogError( ( "Argument cannot be NULL: pContext=%p, "
                    "pPublishInfo=%p.",
                    ( const void * ) pContext,
                    ( const void * ) pPublishInfo ) );
        status = MQTTBadParameter;
    }
    else if( ( pPublishInfo->qos != MQTTQoS0 ) && ( packetId == 0U ) )
    {
        LogError( ( "Packet Id is 0 for PUBLISH with QoS=%u.",
                    ( unsigned int ) pPublishInfo->qos ) );
        status = MQTTBadParameter;
    }
    else if( ( pPublishInfo->payloadLength > 0U ) && ( pPublishInfo->pPayload == NULL ) )
    {
        LogError( ( "A nonzero payload length requires a non-NULL payload: "
                    "payloadLength=%lu, pPayload=%p.",
                    ( unsigned long ) pPublishInfo->payloadLength,
                    pPublishInfo->pPayload ) );
        status = MQTTBadParameter;
    }
    else if( CHECK_SIZE_T_OVERFLOWS_16BIT( pPublishInfo->topicNameLength ) )
    {
        LogError( ( "Topic name length must be less than 65536." ) );
        status = MQTTBadParameter;
    }
    else if( CHECK_SIZE_T_OVERFLOWS_32BIT( pPublishInfo->payloadLength ) ||
             ( pPublishInfo->payloadLength >= MQTT_REMAINING_LENGTH_INVALID ) )
    {
        LogError( ( "pPublishInfo->payloadLength must be less than %" PRIu32, MQTT_REMAINING_LENGTH_INVALID ) );
        status = MQTTBadParameter;
    }
    else if( ( pContext->outgoingPublishRecords == NULL ) && ( pPublishInfo->qos > MQTTQoS0 ) )
    {
        LogError( ( "Trying to publish a QoS > MQTTQoS0 packet when outgoing publishes "
                    "for QoS1/QoS2 have not been enabled. Please, call MQTT_InitStatefulQoS "
                    "to initialize and enable the use of QoS1/QoS2 publishes." ) );
        status = MQTTBadParameter;
    }
    else
    {
        /* MISRA else */
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t validateTopicFilter( const MQTTContext_t * pContext,
                                         const MQTTSubscribeInfo_t * pSubscriptionList,
                                         size_t iterator,
                                         MQTTSubscriptionType_t subscriptionType )
{
    MQTTStatus_t status = MQTTSuccess;

    if( ( pSubscriptionList[ iterator ].pTopicFilter == NULL ) ||
        ( pSubscriptionList[ iterator ].topicFilterLength == 0U ) )
    {
        LogError( ( "Invalid subscription at index %lu: Topic filter is NULL or has zero length.",
                    ( unsigned long ) iterator ) );
        status = MQTTBadParameter;
    }

    if( ( status == MQTTSuccess ) &&
        CHECK_SIZE_T_OVERFLOWS_16BIT( pSubscriptionList[ iterator ].topicFilterLength ) )
    {
        LogError( ( "Topic filter length must be less than 65536 for topic number %" PRIu32, ( uint32_t ) iterator ) );
        status = MQTTBadParameter;
    }

    if( ( status == MQTTSuccess ) && ( subscriptionType == MQTT_TYPE_SUBSCRIBE ) )
    {
        if( pSubscriptionList[ iterator ].qos > MQTTQoS2 )
        {
            LogError( ( "Protocol Error : QoS cannot be greater than 2" ) );
            status = MQTTBadParameter;
        }
        else if( checkWildcardSubscriptions( pContext->connectionProperties.isWildcardAvailable,
                                             pSubscriptionList,
                                             iterator ) )
        {
            LogError( ( "Protocol Error : Wildcard Subscriptions not allowed. " ) );
            status = MQTTBadParameter;
        }
        else if( pSubscriptionList[ iterator ].retainHandlingOption > retainDoNotSendonSub )
        {
            LogError( ( "Protocol Error : retainHandlingOption cannot be greater than 2" ) );
            status = MQTTBadParameter;
        }
        else
        {
            status = validateSharedSubscriptions( pContext,
                                                  pSubscriptionList,
                                                  iterator );
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static bool checkWildcardSubscriptions( uint8_t isWildcardAvailable,
                                        const MQTTSubscribeInfo_t * pSubscriptionList,
                                        size_t iterator )
{
    bool ret = false;

    if( isWildcardAvailable == 0U )
    {
        if( ( ( strchr( pSubscriptionList[ iterator ].pTopicFilter, ( int32_t ) '#' ) != NULL ) ||
              ( strchr( pSubscriptionList[ iterator ].pTopicFilter, ( int32_t ) '+' ) != NULL ) ) )
        {
            ret = true;
        }
    }

    return ret;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t validateSharedSubscriptions( const MQTTContext_t * pContext,
                                                 const MQTTSubscribeInfo_t * pSubscriptionList,
                                                 const size_t iterator )
{
    MQTTStatus_t status = MQTTSuccess;
    uint16_t topicFilterLength;
    bool isSharedSub;
    const char * shareNameEnd;
    const char * shareNameStart;

    assert( !CHECK_SIZE_T_OVERFLOWS_16BIT( pSubscriptionList[ iterator ].topicFilterLength ) );

    topicFilterLength = ( uint16_t ) pSubscriptionList[ iterator ].topicFilterLength;
    isSharedSub = ( topicFilterLength > 7U );

    /* Need to check this only if the length is proper. */
    if( pSubscriptionList[ iterator ].topicFilterLength > 7U )
    {
        isSharedSub = ( isSharedSub ) && ( ( strncmp( pSubscriptionList[ iterator ].pTopicFilter, "$share/", 7U ) ) == 0 );
    }

    if( isSharedSub )
    {
        shareNameStart = &( pSubscriptionList[ iterator ].pTopicFilter[ 7U ] );
        shareNameEnd = memchr( shareNameStart, ( int32_t ) '/', ( size_t ) topicFilterLength - 7U );

        if( ( shareNameEnd == NULL ) ||
            ( shareNameEnd == &( pSubscriptionList[ iterator ].pTopicFilter[ 7 ] ) ) )
        {
            LogError( ( "Protocol Error : ShareName is not present , missing or empty" ) );
            status = MQTTBadParameter;
        }
        else if( pSubscriptionList[ iterator ].noLocalOption )
        {
            LogError( ( "Protocol Error : noLocalOption cannot be 1 for shared subscriptions" ) );
            status = MQTTBadParameter;
        }
        else if( pContext->connectionProperties.isSharedAvailable == 0U )
        {
            LogError( ( "Protocol Error : Shared Subscriptions not allowed" ) );
            status = MQTTBadParameter;
        }
        else if( shareNameEnd == &( pSubscriptionList[ iterator ].pTopicFilter[ topicFilterLength - 1U ] ) )
        {
            LogError( ( "Protocol Error : Topic filter after share name is missing" ) );
            status = MQTTBadParameter;
        }
        else
        {
            const char * ptr;

            for( ptr = shareNameStart; ptr < shareNameEnd; ptr++ )
            {
                if( ( *ptr == '#' ) || ( *ptr == '+' ) )
                {
                    status = MQTTBadParameter;
                    break; /* Invalid share name */
                }
            }
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static void addSubscriptionOptions( const MQTTSubscribeInfo_t subscriptionInfo,
                                    uint8_t * pSubscriptionOptionsArray,
                                    size_t currentOptionIndex )
{
    uint8_t subscriptionOptions = 0U;

    if( subscriptionInfo.qos == MQTTQoS1 )
    {
        LogInfo( ( "Adding QoS as QoS 1 in SUBSCRIBE payload" ) );
        UINT8_SET_BIT( subscriptionOptions, MQTT_SUBSCRIBE_QOS1 );
    }
    else if( subscriptionInfo.qos == MQTTQoS2 )
    {
        LogInfo( ( "Adding QoS as QoS 2 in SUBSCRIBE payload" ) );
        UINT8_SET_BIT( subscriptionOptions, MQTT_SUBSCRIBE_QOS2 );
    }
    else
    {
        LogInfo( ( "Adding QoS as QoS 0 in SUBSCRIBE payload" ) );
    }

    if( subscriptionInfo.noLocalOption )
    {
        LogInfo( ( "Adding noLocalOption in SUBSCRIBE payload" ) );
        UINT8_SET_BIT( subscriptionOptions, MQTT_SUBSCRIBE_NO_LOCAL );
    }
    else
    {
        LogDebug( ( "Adding noLocalOption as 0 in SUBSCRIBE payload" ) );
    }

    if( subscriptionInfo.retainAsPublishedOption )
    {
        LogInfo( ( " retainAsPublishedOption in SUBSCRIBE payload" ) );
        UINT8_SET_BIT( subscriptionOptions, MQTT_SUBSCRIBE_RETAIN_AS_PUBLISHED );
    }
    else
    {
        LogDebug( ( "retainAsPublishedOption as 0 in SUBSCRIBE payload" ) );
    }

    if( subscriptionInfo.retainHandlingOption == retainSendOnSub )
    {
        LogInfo( ( "Send Retain messages at the time of subscribe" ) );
    }
    else if( subscriptionInfo.retainHandlingOption == retainSendOnSubIfNotPresent )
    {
        LogInfo( ( "Send retained messages at subscribe only if the subscription does not currently exist" ) );
        UINT8_SET_BIT( subscriptionOptions, MQTT_SUBSCRIBE_RETAIN_HANDLING1 );
    }
    else
    {
        LogInfo( ( "Do not send retained messages at subscribe" ) );
        UINT8_SET_BIT( subscriptionOptions, MQTT_SUBSCRIBE_RETAIN_HANDLING2 );
    }

    pSubscriptionOptionsArray[ currentOptionIndex ] = subscriptionOptions;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t handleSubUnsubAck( MQTTContext_t * pContext,
                                       MQTTPacketInfo_t * pIncomingPacket )
{
    MQTTStatus_t status = MQTTSuccess;
    uint16_t packetIdentifier;
    MQTTEventCallback_t appCallback;
    MQTTDeserializedInfo_t deserializedInfo;
    MQTTPropBuilder_t propBuffer = { 0 };

    MQTTReasonCodeInfo_t ackInfo = { 0 };

    assert( pContext != NULL );
    assert( pIncomingPacket != NULL );
    assert( pContext->appCallback != NULL );

    appCallback = pContext->appCallback;

    status = MQTT_DeserializeAck( pIncomingPacket,
                                  &packetIdentifier,
                                  &ackInfo,
                                  &propBuffer,
                                  &pContext->connectionProperties );

    LogInfo( ( "Ack packet deserialized with result: %s.",
               MQTT_Status_strerror( status ) ) );

    if( status == MQTTSuccess )
    {
        deserializedInfo.packetIdentifier = packetIdentifier;
        deserializedInfo.deserializationResult = status;
        deserializedInfo.pPublishInfo = NULL;
        deserializedInfo.pReasonCode = &ackInfo;

        /* Invoke application callback to hand the buffer over to application */
        if( appCallback( pContext, pIncomingPacket, &deserializedInfo, NULL,
                         NULL, &propBuffer ) == false )
        {
            status = MQTTEventCallbackFailed;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t sendDisconnectWithoutCopy( MQTTContext_t * pContext,
                                               const MQTTSuccessFailReasonCode_t * pReasonCode,
                                               uint32_t remainingLength,
                                               const MQTTPropBuilder_t * pPropertyBuilder )
{
    int32_t bytesSentOrError;
    size_t ioVectorLength = 0U;
    uint32_t totalMessageLength = 0U;
    uint32_t disconnectPropLen = 0U;
    MQTTStatus_t status = MQTTSuccess;

    /* Maximum number of bytes required by the fixed size part of the CONNECT
     * packet header according to the MQTT specification.
     * MQTT Control Byte      0 + 1 = 1
     * Remaining length (max)   + 4 = 5
     * Reason Code              + 1 = 6
     *
     * Note that the reason code is not actually 'fixed'. But it avoids much
     * calculation and potential TCP/TLS overhead in some implementations later
     * at the cost of one byte on the stack.
     */
    uint8_t fixedHeader[ 6U ];

    /**
     * Maximum number of bytes to send the Property Length.
     * Property Length  0 + 4 = 4
     */
    uint8_t propertyLength[ 4U ];

    /* The maximum vectors required to encode and send a disconnect packet. The
     * breakdown is shown below.
     * disconnect Header    0 + 1 = 1
     * Property Length        + 1 = 2
     * Optional Properties    + 1 = 3
     * */
    TransportOutVector_t pIoVector[ 3U ];

    uint8_t * pIndex = fixedHeader;
    TransportOutVector_t * iterator = pIoVector;

    assert( pContext != NULL );
    assert( remainingLength < MQTT_REMAINING_LENGTH_INVALID );

    if( pPropertyBuilder != NULL )
    {
        assert( pReasonCode != NULL );
    }

    /* Only for fixed size fields. */
    pIndex = serializeDisconnectFixed( pIndex, pReasonCode, remainingLength );
    iterator->iov_base = fixedHeader;
    /* More details at: https://github.com/FreeRTOS/coreMQTT/blob/main/MISRA.md#rule-182 */
    /* More details at: https://github.com/FreeRTOS/coreMQTT/blob/main/MISRA.md#rule-108 */
    /* coverity[misra_c_2012_rule_18_2_violation] */
    /* coverity[misra_c_2012_rule_10_8_violation] */
    iterator->iov_len = ( size_t ) ( pIndex - fixedHeader );
    assert( iterator->iov_len <= 6U );
    totalMessageLength += ( uint32_t ) iterator->iov_len;
    iterator++;
    ioVectorLength++;

    if( ( pPropertyBuilder != NULL ) && ( pPropertyBuilder->pBuffer != NULL ) )
    {
        disconnectPropLen = ( uint32_t ) pPropertyBuilder->currentIndex;
    }

    pIndex = encodeVariableLength( propertyLength, disconnectPropLen );
    iterator->iov_base = propertyLength;
    /* More details at: https://github.com/FreeRTOS/coreMQTT/blob/main/MISRA.md#rule-182 */
    /* More details at: https://github.com/FreeRTOS/coreMQTT/blob/main/MISRA.md#rule-108 */
    /* coverity[misra_c_2012_rule_18_2_violation] */
    /* coverity[misra_c_2012_rule_10_8_violation] */
    iterator->iov_len = ( size_t ) ( pIndex - propertyLength );
    totalMessageLength += ( uint32_t ) iterator->iov_len;
    iterator++;
    ioVectorLength++;

    if( disconnectPropLen > 0U )
    {
        iterator->iov_base = pPropertyBuilder->pBuffer;
        iterator->iov_len = pPropertyBuilder->currentIndex;

        if( ADDITION_WILL_OVERFLOW_U32( totalMessageLength, pPropertyBuilder->currentIndex ) ||
            ( ( totalMessageLength + pPropertyBuilder->currentIndex ) > MQTT_MAX_PACKET_SIZE ) )
        {
            LogError( ( "Total MQTT packet size must be less than 268435461" ) );
            status = MQTTBadParameter;
        }
        else
        {
            totalMessageLength += ( uint32_t ) iterator->iov_len;
            iterator++;
            ioVectorLength++;
        }
    }

    if( status == MQTTSuccess )
    {
        bytesSentOrError = sendMessageVector( pContext, pIoVector, ioVectorLength );

        if( bytesSentOrError != ( int32_t ) totalMessageLength )
        {
            status = MQTTSendFailed;
            LogError( ( "Failed to send disconnect packet." ) );
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_Init( MQTTContext_t * pContext,
                        const TransportInterface_t * pTransportInterface,
                        MQTTGetCurrentTimeFunc_t getTimeFunction,
                        MQTTEventCallback_t userCallback,
                        const MQTTFixedBuffer_t * pNetworkBuffer )
{
    MQTTStatus_t status = MQTTSuccess;

    /* Validate arguments. */
    if( ( pContext == NULL ) || ( pTransportInterface == NULL ) ||
        ( pNetworkBuffer == NULL ) )
    {
        LogError( ( "Argument cannot be NULL: pContext=%p, "
                    "pTransportInterface=%p, "
                    "pNetworkBuffer=%p",
                    ( void * ) pContext,
                    ( const void * ) pTransportInterface,
                    ( const void * ) pNetworkBuffer ) );
        status = MQTTBadParameter;
    }
    else if( getTimeFunction == NULL )
    {
        LogError( ( "Invalid parameter: getTimeFunction is NULL" ) );
        status = MQTTBadParameter;
    }
    else if( userCallback == NULL )
    {
        LogError( ( "Invalid parameter: userCallback is NULL" ) );
        status = MQTTBadParameter;
    }
    else if( pTransportInterface->recv == NULL )
    {
        LogError( ( "Invalid parameter: pTransportInterface->recv is NULL" ) );
        status = MQTTBadParameter;
    }
    else if( pTransportInterface->send == NULL )
    {
        LogError( ( "Invalid parameter: pTransportInterface->send is NULL" ) );
        status = MQTTBadParameter;
    }
    else
    {
        ( void ) memset( pContext, 0x00, sizeof( MQTTContext_t ) );

        pContext->connectStatus = MQTTNotConnected;
        pContext->transportInterface = *pTransportInterface;
        pContext->getTime = getTimeFunction;
        pContext->appCallback = userCallback;
        pContext->networkBuffer = *pNetworkBuffer;
        pContext->ackPropsBuffer.pBuffer = NULL;

        /* Zero is not a valid packet ID per MQTT spec. Start from 1. */
        pContext->nextPacketId = 1;

        /* Setting default connect properties in our application */
        status = MQTT_InitConnect( &( pContext->connectionProperties ) );
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_InitStatefulQoS( MQTTContext_t * pContext,
                                   MQTTPubAckInfo_t * pOutgoingPublishRecords,
                                   size_t outgoingPublishCount,
                                   MQTTPubAckInfo_t * pIncomingPublishRecords,
                                   size_t incomingPublishCount,
                                   uint8_t * pAckPropsBuf,
                                   size_t ackPropsBufLength )
{
    MQTTStatus_t status = MQTTSuccess;

    if( pContext == NULL )
    {
        LogError( ( "Argument cannot be NULL: pContext=%p\n",
                    ( void * ) pContext ) );
        status = MQTTBadParameter;
    }

    /* Check whether the arguments make sense. Not equal here behaves
     * like an exclusive-or operator for boolean values. */
    else if( ( outgoingPublishCount == 0U ) !=
             ( pOutgoingPublishRecords == NULL ) )
    {
        LogError( ( "Arguments do not match: pOutgoingPublishRecords=%p, "
                    "outgoingPublishCount=%lu",
                    ( void * ) pOutgoingPublishRecords,
                    ( unsigned long ) outgoingPublishCount ) );
        status = MQTTBadParameter;
    }

    /* Check whether the arguments make sense. Not equal here behaves
     * like an exclusive-or operator for boolean values. */
    else if( ( incomingPublishCount == 0U ) !=
             ( pIncomingPublishRecords == NULL ) )
    {
        LogError( ( "Arguments do not match: pIncomingPublishRecords=%p, "
                    "incomingPublishCount=%lu",
                    ( void * ) pIncomingPublishRecords,
                    ( unsigned long ) incomingPublishCount ) );
        status = MQTTBadParameter;
    }
    else if( pContext->appCallback == NULL )
    {
        LogError( ( "MQTT_InitStatefulQoS must be called only after MQTT_Init has"
                    " been called successfully.\n" ) );
        status = MQTTBadParameter;
    }
    else
    {
        pContext->incomingPublishRecordMaxCount = incomingPublishCount;
        pContext->incomingPublishRecords = pIncomingPublishRecords;
        pContext->outgoingPublishRecordMaxCount = outgoingPublishCount;
        pContext->outgoingPublishRecords = pOutgoingPublishRecords;

        if( ( pAckPropsBuf != NULL ) && ( ackPropsBufLength != 0U ) )
        {
            status = MQTTPropertyBuilder_Init( &pContext->ackPropsBuffer, pAckPropsBuf, ackPropsBufLength );
        }
        else
        {
            pContext->ackPropsBuffer.pBuffer = NULL;
            pContext->ackPropsBuffer.bufferLength = 0;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_InitRetransmits( MQTTContext_t * pContext,
                                   MQTTStorePacketForRetransmit storeFunction,
                                   MQTTRetrievePacketForRetransmit retrieveFunction,
                                   MQTTClearPacketForRetransmit clearFunction )
{
    MQTTStatus_t status = MQTTSuccess;

    if( pContext == NULL )
    {
        LogError( ( "Argument cannot be NULL: pContext=%p\n",
                    ( void * ) pContext ) );
        status = MQTTBadParameter;
    }
    else if( storeFunction == NULL )
    {
        LogError( ( "Invalid parameter: storeFunction is NULL" ) );
        status = MQTTBadParameter;
    }
    else if( retrieveFunction == NULL )
    {
        LogError( ( "Invalid parameter: retrieveFunction is NULL" ) );
        status = MQTTBadParameter;
    }
    else if( clearFunction == NULL )
    {
        LogError( ( "Invalid parameter: clearFunction is NULL" ) );
        status = MQTTBadParameter;
    }
    else
    {
        pContext->storeFunction = storeFunction;
        pContext->retrieveFunction = retrieveFunction;
        pContext->clearFunction = clearFunction;
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_CancelCallback( const MQTTContext_t * pContext,
                                  uint16_t packetId )
{
    MQTTStatus_t status = MQTTSuccess;

    if( pContext == NULL )
    {
        LogWarn( ( "pContext is NULL\n" ) );
        status = MQTTBadParameter;
    }
    else if( pContext->outgoingPublishRecords == NULL )
    {
        LogError( ( "QoS1/QoS2 is not initialized for use. Please "
                    "call MQTT_InitStatefulQoS to enable QoS1 and QoS2 "
                    "publishes.\n" ) );
        status = MQTTBadParameter;
    }
    else
    {
        MQTT_PRE_STATE_UPDATE_HOOK( pContext );

        status = MQTT_RemoveStateRecord( pContext,
                                         packetId );

        MQTT_POST_STATE_UPDATE_HOOK( pContext );
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_CheckConnectStatus( const MQTTContext_t * pContext )
{
    MQTTConnectionStatus_t connectStatus;
    MQTTStatus_t status = MQTTSuccess;

    if( pContext == NULL )
    {
        LogError( ( "Argument cannot be NULL: pContext=%p",
                    ( const void * ) pContext ) );
        status = MQTTBadParameter;
    }

    if( status == MQTTSuccess )
    {
        MQTT_PRE_STATE_UPDATE_HOOK( pContext );

        connectStatus = pContext->connectStatus;

        MQTT_POST_STATE_UPDATE_HOOK( pContext );

        switch( connectStatus )
        {
            case MQTTConnected:
                status = MQTTStatusConnected;
                break;

            case MQTTDisconnectPending:
                status = MQTTStatusDisconnectPending;
                break;

            default:
                status = MQTTStatusNotConnected;
                break;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_Connect( MQTTContext_t * pContext,
                           const MQTTConnectInfo_t * pConnectInfo,
                           const MQTTPublishInfo_t * pWillInfo,
                           uint32_t timeoutMs,
                           bool * pSessionPresent,
                           MQTTPropBuilder_t * pPropertyBuilder,
                           const MQTTPropBuilder_t * pWillPropertyBuilder )
{
    uint32_t remainingLength = 0U;
    uint32_t packetSize = 0U;
    MQTTStatus_t status = MQTTSuccess;
    MQTTPacketInfo_t incomingPacket = { 0 };
    MQTTConnectionStatus_t connectStatus;
    uint8_t backupPropBuffer[ 5 ];
    MQTTPropBuilder_t backupPropBuilder = { 0 };
    MQTTPropBuilder_t * pBackupPropBuilder = pPropertyBuilder;

    if( ( pContext == NULL ) || ( pConnectInfo == NULL ) || ( pSessionPresent == NULL ) )
    {
        LogError( ( "Argument cannot be NULL: pContext=%p, "
                    "pConnectInfo=%p, pSessionPresent=%p.",
                    ( void * ) pContext,
                    ( const void * ) pConnectInfo,
                    ( void * ) pSessionPresent ) );
        status = MQTTBadParameter;
    }

    if( ( status == MQTTSuccess ) && ( pWillInfo != NULL ) && ( pWillPropertyBuilder != NULL ) )
    {
        status = MQTT_ValidateWillProperties( pWillPropertyBuilder );
    }

    if( status == MQTTSuccess )
    {
        if( pBackupPropBuilder != NULL )
        {
            bool isRequestProblemInfoSet = false;
            uint32_t packetMaxSize = UINT32_MAX;
            status = MQTT_ValidateConnectProperties( pBackupPropBuilder,
                                                     &isRequestProblemInfoSet,
                                                     &packetMaxSize );

            /* Update the field in the context so that it can be gated on. Note that we
             * did not intentionally check the result of the above API call as it will be
             * checked later. Even if the call fails, we will set the variable in the
             * context incorrectly which is fine. */
            pContext->connectionProperties.requestProblemInfo = isRequestProblemInfoSet;

            if( packetMaxSize > pContext->networkBuffer.size )
            {
                LogError( ( "Properties have packet maximum set to %" PRIu32
                            " whereas the buffer length is %" PRIu32
                            ". Please make sure that buffer is at least as big as %" PRIu32
                            " otherwise the server can send a bigger packet which cannot be processed by the coreMQTT library.",
                            packetMaxSize,
                            ( uint32_t ) pContext->networkBuffer.size,
                            packetMaxSize ) );
                status = MQTTBadParameter;
            }
        }
        else
        {
            uint32_t maxPacketSize;
            backupPropBuilder.pBuffer = backupPropBuffer;
            backupPropBuilder.bufferLength = sizeof( backupPropBuffer );

            pBackupPropBuilder = &backupPropBuilder;

            if( CHECK_SIZE_T_OVERFLOWS_32BIT( pContext->networkBuffer.size ) )
            {
                maxPacketSize = 0xFFFFFFFFU;
            }
            else
            {
                maxPacketSize = ( uint32_t ) pContext->networkBuffer.size;
            }

            LogInfo( ( "Application has not set any properties. Adding a property to set the maximum "
                       "packet size received from the server for the client to be %" PRIu32 ".",
                       maxPacketSize ) );
            status = MQTTPropAdd_MaxPacketSize( pBackupPropBuilder,
                                                maxPacketSize,
                                                NULL );
        }
    }

    if( status == MQTTSuccess )
    {
        /* Get MQTT connect packet size and remaining length. */
        status = MQTT_GetConnectPacketSize( pConnectInfo,
                                            pWillInfo,
                                            pBackupPropBuilder,
                                            pWillPropertyBuilder,
                                            &remainingLength,
                                            &packetSize );
        /* coverity[sensitive_data_leak] */
        LogDebug( ( "CONNECT packet size is %lu and remaining length is %lu.",
                    ( unsigned long ) packetSize,
                    ( unsigned long ) remainingLength ) );
    }

    if( status == MQTTSuccess )
    {
        MQTT_PRE_STATE_UPDATE_HOOK( pContext );

        connectStatus = pContext->connectStatus;

        if( connectStatus != MQTTNotConnected )
        {
            status = ( connectStatus == MQTTConnected ) ? MQTTStatusConnected : MQTTStatusDisconnectPending;
        }

        if( status == MQTTSuccess )
        {
            status = sendConnectWithoutCopy( pContext,
                                             pConnectInfo,
                                             pWillInfo,
                                             remainingLength,
                                             pBackupPropBuilder,
                                             pWillPropertyBuilder );
        }

        /* TODO: As part of CONNECT/CONNACK setup, there can be AUTH packets sent.
         * It is not dealt with currently. */

        /* Read CONNACK from transport layer. */
        if( status == MQTTSuccess )
        {
            status = receiveConnack( pContext,
                                     timeoutMs,
                                     pConnectInfo->cleanSession,
                                     &incomingPacket,
                                     pSessionPresent );
        }

        /**
         * Update the maximum number of concurrent incoming and outgoing PUBLISH records
         * based on MQTT 5.0 Receive Maximum property :
         *
         * - For incoming publishes: Use the minimum between the client's configured receive maximum
         *   (In the MQTT_Init function) and the receive maximum value sent in CONNECT properties
         *
         * - For outgoing publishes: Use the minimum between the client's configured maximum
         *   (In the MQTT_Init function) and the server's receive maximum value received in CONNACK properties
         **/
        if( status == MQTTSuccess )
        {
            if( pContext->connectionProperties.receiveMax < pContext->incomingPublishRecordMaxCount )
            {
                pContext->incomingPublishRecordMaxCount = pContext->connectionProperties.receiveMax;
            }

            if( pContext->connectionProperties.serverReceiveMax < pContext->outgoingPublishRecordMaxCount )
            {
                pContext->outgoingPublishRecordMaxCount = pContext->connectionProperties.serverReceiveMax;
            }
        }

        if( ( status == MQTTSuccess ) && ( *pSessionPresent != true ) )
        {
            status = handleCleanSession( pContext );
        }

        if( status == MQTTSuccess )
        {
            pContext->connectStatus = MQTTConnected;

            /**
             * Initialize the client's keep-alive timer using the Server Keep Alive value
             * received in the CONNACK.
             * This value overrides the client's original keep-alive setting,
             * as per MQTT v5 specification.
             */
            pContext->keepAliveIntervalSec = pContext->connectionProperties.serverKeepAlive;
            pContext->waitingForPingResp = false;
            pContext->pingReqSendTimeMs = 0U;
        }

        MQTT_POST_STATE_UPDATE_HOOK( pContext );
    }

    if( ( status == MQTTSuccess ) && ( *pSessionPresent == true ) )
    {
        /* Resend PUBRELs and PUBLISHES when reestablishing a session */
        status = handleUncleanSessionResumption( pContext );
    }

    if( status == MQTTSuccess )
    {
        LogInfo( ( "MQTT connection established with the broker." ) );
    }
    else if( ( status == MQTTStatusConnected ) || ( status == MQTTStatusDisconnectPending ) )
    {
        LogInfo( ( "MQTT Connection is either already established or a disconnect is pending, return status = %s.",
                   MQTT_Status_strerror( status ) ) );
    }
    else if( pContext == NULL )
    {
        LogError( ( "MQTT connection failed with status = %s.",
                    MQTT_Status_strerror( status ) ) );
    }
    else
    {
        LogError( ( "MQTT connection failed with status = %s.",
                    MQTT_Status_strerror( status ) ) );

        MQTT_PRE_STATE_UPDATE_HOOK( pContext );

        if( pContext->connectStatus == MQTTConnected )
        {
            /* This will only be executed if after the connack is received
             * the retransmits fail for some reason on an unclean session
             * connection. In this case we need to retry the re-transmits
             * which can only be done using the connect API and that can only
             * be done once we are disconnected, hence we ask the user to
             * call disconnect here */
            pContext->connectStatus = MQTTDisconnectPending;
        }

        MQTT_POST_STATE_UPDATE_HOOK( pContext );
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_Subscribe( MQTTContext_t * pContext,
                             const MQTTSubscribeInfo_t * pSubscriptionList,
                             size_t subscriptionCount,
                             uint16_t packetId,
                             const MQTTPropBuilder_t * pPropertyBuilder )
{
    MQTTConnectionStatus_t connectStatus;
    uint32_t remainingLength = 0U;
    uint32_t packetSize = 0U;
    MQTTStatus_t status = MQTTSuccess;

    status = validateSubscribeUnsubscribeParams( pContext,
                                                 pSubscriptionList,
                                                 subscriptionCount,
                                                 packetId,
                                                 MQTT_TYPE_SUBSCRIBE );

    if( ( status == MQTTSuccess ) && ( pPropertyBuilder != NULL ) && ( pPropertyBuilder->pBuffer != NULL ) )
    {
        bool isSubscriptionIdAvailable;
        assert( ( pContext->connectionProperties.isSubscriptionIdAvailable == 0U ) ||
                ( pContext->connectionProperties.isSubscriptionIdAvailable == 1U ) );

        isSubscriptionIdAvailable = ( pContext->connectionProperties.isSubscriptionIdAvailable != 0U );
        status = MQTT_ValidateSubscribeProperties( isSubscriptionIdAvailable,
                                                   pPropertyBuilder );
    }

    if( status == MQTTSuccess )
    {
        /* Get the remaining length and packet size. */
        status = MQTT_GetSubscribePacketSize( pSubscriptionList,
                                              subscriptionCount,
                                              pPropertyBuilder,
                                              &remainingLength,
                                              &packetSize,
                                              pContext->connectionProperties.serverMaxPacketSize );
        LogDebug( ( "SUBSCRIBE packet size is %lu and remaining length is %lu.",
                    ( unsigned long ) packetSize,
                    ( unsigned long ) remainingLength ) );
    }

    if( status == MQTTSuccess )
    {
        MQTT_PRE_STATE_UPDATE_HOOK( pContext );

        connectStatus = pContext->connectStatus;

        if( connectStatus != MQTTConnected )
        {
            status = ( connectStatus == MQTTNotConnected ) ? MQTTStatusNotConnected : MQTTStatusDisconnectPending;
        }

        if( status == MQTTSuccess )
        {
            /* Send MQTT SUBSCRIBE packet. */
            status = sendSubscribeWithoutCopy( pContext,
                                               pSubscriptionList,
                                               subscriptionCount,
                                               packetId,
                                               remainingLength,
                                               pPropertyBuilder );
        }

        MQTT_POST_STATE_UPDATE_HOOK( pContext );
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_Publish( MQTTContext_t * pContext,
                           const MQTTPublishInfo_t * pPublishInfo,
                           uint16_t packetId,
                           const MQTTPropBuilder_t * pPropertyBuilder )
{
    size_t headerSize = 0U;
    uint32_t remainingLength = 0U;
    uint32_t packetSize = 0U;
    MQTTPublishState_t publishStatus = MQTTStateNull;
    MQTTConnectionStatus_t connectStatus;
    uint16_t topicAlias = 0U;

    /* Maximum number of bytes required by the 'fixed' part of the PUBLISH
     * packet header according to the MQTT specifications.
     * Header byte           0 + 1 = 1
     * Length (max)            + 4 = 5
     * Topic string length     + 2 = 7
     *
     * Note that since publish is one of the most common operations in MQTT
     * connection, we have moved the topic string length to the 'fixed' part of
     * the header so efficiency. Otherwise, we would need an extra vector and
     * an extra call to 'send' (in case writev is not defined) to send the
     * topic length.    */
    uint8_t mqttHeader[ 7U ];
    MQTTStatus_t status = MQTTSuccess;

    /* Validate arguments. */
    status = validatePublishParams( pContext, pPublishInfo, packetId );

    /* Validate Publish Properties and extract Topic Alias from the properties. */
    if( ( status == MQTTSuccess ) && ( pPropertyBuilder != NULL ) && ( pPropertyBuilder->pBuffer != NULL ) )
    {
        status = MQTT_ValidatePublishProperties( pContext->connectionProperties.serverTopicAliasMax,
                                                 pPropertyBuilder, &topicAlias );
    }

    if( status == MQTTSuccess )
    {
        /* Validate Publish Properties with the persistent Connection Properties. */
        status = MQTT_ValidatePublishParams( pPublishInfo,
                                             pContext->connectionProperties.retainAvailable,
                                             pContext->connectionProperties.serverMaxQos,
                                             topicAlias,
                                             pContext->connectionProperties.serverMaxPacketSize );
    }

    if( status == MQTTSuccess )
    {
        /* Get the remaining length and packet size. */
        status = MQTT_GetPublishPacketSize( pPublishInfo,
                                            pPropertyBuilder,
                                            &remainingLength,
                                            &packetSize,
                                            pContext->connectionProperties.serverMaxPacketSize );
    }

    if( status == MQTTSuccess )
    {
        status = MQTT_SerializePublishHeaderWithoutTopic( pPublishInfo,
                                                          remainingLength,
                                                          mqttHeader,
                                                          &headerSize );
    }

    if( status == MQTTSuccess )
    {
        assert( headerSize <= 7U );

        /* Take the mutex as multiple send calls are required for sending this
         * packet. */
        MQTT_PRE_STATE_UPDATE_HOOK( pContext );

        connectStatus = pContext->connectStatus;

        if( connectStatus != MQTTConnected )
        {
            status = ( connectStatus == MQTTNotConnected ) ? MQTTStatusNotConnected : MQTTStatusDisconnectPending;
        }

        if( ( status == MQTTSuccess ) && ( pPublishInfo->qos > MQTTQoS0 ) )
        {
            /* Set the flag so that the corresponding hook can be called later. */

            status = MQTT_ReserveState( pContext,
                                        packetId,
                                        pPublishInfo->qos );

            /* State already exists for a duplicate packet.
             * If a state doesn't exist, it will be handled as a new publish in
             * state engine. */
            if( ( status == MQTTStateCollision ) && ( pPublishInfo->dup == true ) )
            {
                status = MQTTSuccess;
            }
        }

        if( status == MQTTSuccess )
        {
            status = sendPublishWithoutCopy( pContext,
                                             pPublishInfo,
                                             mqttHeader,
                                             headerSize,
                                             packetId,
                                             pPropertyBuilder );
        }

        if( ( status == MQTTSuccess ) &&
            ( pPublishInfo->qos > MQTTQoS0 ) )
        {
            /* Update state machine after PUBLISH is sent.
             * Only to be done for QoS1 or QoS2. */
            status = MQTT_UpdateStatePublish( pContext,
                                              packetId,
                                              MQTT_SEND,
                                              pPublishInfo->qos,
                                              &publishStatus );

            if( status != MQTTSuccess )
            {
                LogError( ( "Update state for publish failed with status %s."
                            " However PUBLISH packet was sent to the broker."
                            " Any further handling of ACKs for the packet Id"
                            " will fail.",
                            MQTT_Status_strerror( status ) ) );
            }
        }

        /* mutex should be released and not before updating the state
         * because we need to make sure that the state is updated
         * after sending the publish packet, before the receive
         * loop receives ack for this and would want to update its state
         */
        MQTT_POST_STATE_UPDATE_HOOK( pContext );
    }

    if( status != MQTTSuccess )
    {
        LogError( ( "MQTT PUBLISH failed with status %s.",
                    MQTT_Status_strerror( status ) ) );
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_Ping( MQTTContext_t * pContext )
{
    int32_t sendResult = 0;
    MQTTStatus_t status = MQTTSuccess;
    uint32_t packetSize = 0U;
    /* MQTT ping packets are of fixed length. */
    uint8_t pingreqPacket[ 2U ];
    MQTTFixedBuffer_t localBuffer;
    MQTTConnectionStatus_t connectStatus;

    localBuffer.pBuffer = pingreqPacket;
    localBuffer.size = sizeof( pingreqPacket );

    if( pContext == NULL )
    {
        LogError( ( "pContext is NULL." ) );
        status = MQTTBadParameter;
    }

    if( status == MQTTSuccess )
    {
        /* Get MQTT PINGREQ packet size. */
        status = MQTT_GetPingreqPacketSize( &packetSize );

        if( status == MQTTSuccess )
        {
            assert( packetSize == localBuffer.size );
            LogDebug( ( "MQTT PINGREQ packet size is %lu.",
                        ( unsigned long ) packetSize ) );
        }
        else
        {
            LogError( ( "Failed to get the PINGREQ packet size." ) );
        }
    }

    if( status == MQTTSuccess )
    {
        /* Serialize MQTT PINGREQ. */
        status = MQTT_SerializePingreq( &localBuffer );
    }

    if( status == MQTTSuccess )
    {
        /* Take the mutex as the send call should not be interrupted in
         * between. */

        MQTT_PRE_STATE_UPDATE_HOOK( pContext );

        connectStatus = pContext->connectStatus;

        if( connectStatus != MQTTConnected )
        {
            status = ( connectStatus == MQTTNotConnected ) ? MQTTStatusNotConnected : MQTTStatusDisconnectPending;
        }

        if( status == MQTTSuccess )
        {
            /* Send the serialized PINGREQ packet to transport layer.
             * Here, we do not use the vectored IO approach for efficiency as the
             * Ping packet does not have numerous fields which need to be copied
             * from the user provided buffers. Thus it can be sent directly. */
            sendResult = sendBuffer( pContext,
                                     localBuffer.pBuffer,
                                     packetSize );

            /* It is an error to not send the entire PINGREQ packet. */
            if( sendResult < ( int32_t ) packetSize )
            {
                LogError( ( "Transport send failed for PINGREQ packet." ) );
                status = MQTTSendFailed;
            }
            else
            {
                pContext->pingReqSendTimeMs = pContext->lastPacketTxTime;
                pContext->waitingForPingResp = true;
                LogDebug( ( "Sent %ld bytes of PINGREQ packet.",
                            ( long int ) sendResult ) );
            }
        }

        MQTT_POST_STATE_UPDATE_HOOK( pContext );
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_Unsubscribe( MQTTContext_t * pContext,
                               const MQTTSubscribeInfo_t * pSubscriptionList,
                               size_t subscriptionCount,
                               uint16_t packetId,
                               const MQTTPropBuilder_t * pPropertyBuilder )
{
    MQTTConnectionStatus_t connectStatus;
    uint32_t remainingLength = 0U;
    uint32_t packetSize = 0U;
    MQTTStatus_t status = MQTTSuccess;

    /* Validate arguments. */
    status = validateSubscribeUnsubscribeParams( pContext,
                                                 pSubscriptionList,
                                                 subscriptionCount,
                                                 packetId,
                                                 MQTT_TYPE_UNSUBSCRIBE );

    if( ( status == MQTTSuccess ) && ( pPropertyBuilder != NULL ) && ( pPropertyBuilder->pBuffer != NULL ) )
    {
        status = MQTT_ValidateUnsubscribeProperties( pPropertyBuilder );
    }

    if( status == MQTTSuccess )
    {
        /* Get the remaining length and packet size. */
        status = MQTT_GetUnsubscribePacketSize( pSubscriptionList,
                                                subscriptionCount,
                                                pPropertyBuilder,
                                                &remainingLength,
                                                &packetSize,
                                                pContext->connectionProperties.serverMaxPacketSize );
        LogInfo( ( "UNSUBSCRIBE packet size is %lu and remaining length is %lu.",
                   ( unsigned long ) packetSize,
                   ( unsigned long ) remainingLength ) );
    }

    if( status == MQTTSuccess )
    {
        /* Take the mutex because the below call should not be interrupted. */
        MQTT_PRE_STATE_UPDATE_HOOK( pContext );

        connectStatus = pContext->connectStatus;

        if( connectStatus != MQTTConnected )
        {
            status = ( connectStatus == MQTTNotConnected ) ? MQTTStatusNotConnected : MQTTStatusDisconnectPending;
        }

        if( status == MQTTSuccess )
        {
            status = sendUnsubscribeWithoutCopy( pContext,
                                                 pSubscriptionList,
                                                 subscriptionCount,
                                                 packetId,
                                                 remainingLength,
                                                 pPropertyBuilder );
        }

        MQTT_POST_STATE_UPDATE_HOOK( pContext );
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_Disconnect( MQTTContext_t * pContext,
                              const MQTTPropBuilder_t * pPropertyBuilder,
                              const MQTTSuccessFailReasonCode_t * pReasonCode )
{
    uint32_t packetSize = 0U;
    uint32_t remainingLength = 0U;
    MQTTStatus_t status = MQTTSuccess;
    MQTTConnectionStatus_t connectStatus;

    /* Validate arguments. */
    if( pContext == NULL )
    {
        LogError( ( "pContext cannot be NULL." ) );
        status = MQTTBadParameter;
    }
    else if( ( pReasonCode == NULL ) && ( pPropertyBuilder != NULL ) )
    {
        LogError( ( "Reason code must be provided if the properties are non-NULL." ) );
        status = MQTTBadParameter;
    }
    else
    {
        /* Parameters are valid. */
    }

    if( ( status == MQTTSuccess ) && ( pPropertyBuilder != NULL ) && ( pPropertyBuilder->pBuffer != NULL ) )
    {
        status = MQTT_ValidateDisconnectProperties( pContext->connectionProperties.sessionExpiry,
                                                    pPropertyBuilder );
    }

    if( status == MQTTSuccess )
    {
        /* Get MQTT DISCONNECT packet size. */
        status = MQTT_GetDisconnectPacketSize( pPropertyBuilder,
                                               &remainingLength,
                                               &packetSize,
                                               pContext->connectionProperties.serverMaxPacketSize,
                                               pReasonCode );
        LogDebug( ( "MQTT DISCONNECT packet size is %lu.",
                    ( unsigned long ) packetSize ) );
    }

    if( status == MQTTSuccess )
    {
        /* Take the mutex because the below call should not be interrupted. */
        MQTT_PRE_STATE_UPDATE_HOOK( pContext );

        connectStatus = pContext->connectStatus;

        if( connectStatus == MQTTNotConnected )
        {
            status = MQTTStatusNotConnected;
        }

        if( status == MQTTSuccess )
        {
            LogInfo( ( "Disconnected from the broker." ) );
            pContext->connectStatus = MQTTNotConnected;

            /* Reset the index and clean the buffer on a successful disconnect. */
            pContext->index = 0;
            ( void ) memset( pContext->networkBuffer.pBuffer, 0, pContext->networkBuffer.size );

            LogInfo( ( "MQTT Connection Disconnected Successfully" ) );

            status = sendDisconnectWithoutCopy( pContext,
                                                pReasonCode,
                                                remainingLength,
                                                pPropertyBuilder );
        }

        MQTT_POST_STATE_UPDATE_HOOK( pContext );
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_ProcessLoop( MQTTContext_t * pContext )
{
    MQTTStatus_t status = MQTTBadParameter;

    if( pContext == NULL )
    {
        LogError( ( "Invalid input parameter: MQTT Context cannot be NULL." ) );
    }
    else if( pContext->getTime == NULL )
    {
        LogError( ( "Invalid input parameter: MQTT Context must have valid getTime." ) );
    }
    else if( pContext->networkBuffer.pBuffer == NULL )
    {
        LogError( ( "Invalid input parameter: The MQTT context's networkBuffer must not be NULL." ) );
    }
    else
    {
        pContext->controlPacketSent = false;
        status = receiveSingleIteration( pContext, true );
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_ReceiveLoop( MQTTContext_t * pContext )
{
    MQTTStatus_t status = MQTTBadParameter;

    if( pContext == NULL )
    {
        LogError( ( "Invalid input parameter: MQTT Context cannot be NULL." ) );
    }
    else if( pContext->getTime == NULL )
    {
        LogError( ( "Invalid input parameter: MQTT Context must have a valid getTime function." ) );
    }
    else if( pContext->networkBuffer.pBuffer == NULL )
    {
        LogError( ( "Invalid input parameter: MQTT context's networkBuffer must not be NULL." ) );
    }
    else
    {
        status = receiveSingleIteration( pContext, false );
    }

    return status;
}

/*-----------------------------------------------------------*/

uint16_t MQTT_GetPacketId( MQTTContext_t * pContext )
{
    uint16_t packetId = 0U;

    if( pContext != NULL )
    {
        MQTT_PRE_STATE_UPDATE_HOOK( pContext );

        packetId = pContext->nextPacketId;

        /* A packet ID of zero is not a valid packet ID. When the max ID
         * is reached the next one should start at 1. */
        if( pContext->nextPacketId == ( uint16_t ) UINT16_MAX )
        {
            pContext->nextPacketId = 1;
        }
        else
        {
            pContext->nextPacketId++;
        }

        MQTT_POST_STATE_UPDATE_HOOK( pContext );
    }

    return packetId;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_MatchTopic( const char * pTopicName,
                              const size_t topicNameLength,
                              const char * pTopicFilter,
                              const size_t topicFilterLength,
                              bool * pIsMatch )
{
    MQTTStatus_t status = MQTTSuccess;
    bool topicFilterStartsWithWildcard = false;
    bool matchStatus = false;

    if( ( pTopicName == NULL ) || ( topicNameLength == 0u ) )
    {
        LogError( ( "Invalid paramater: Topic name should be non-NULL and its "
                    "length should be > 0: TopicName=%p, TopicNameLength=%hu",
                    ( const void * ) pTopicName,
                    ( unsigned short ) topicNameLength ) );

        status = MQTTBadParameter;
    }
    else if( ( pTopicFilter == NULL ) || ( topicFilterLength == 0u ) )
    {
        LogError( ( "Invalid paramater: Topic filter should be non-NULL and "
                    "its length should be > 0: TopicName=%p, TopicFilterLength=%hu",
                    ( const void * ) pTopicFilter,
                    ( unsigned short ) topicFilterLength ) );
        status = MQTTBadParameter;
    }
    else if( pIsMatch == NULL )
    {
        LogError( ( "Invalid paramater: Output parameter, pIsMatch, is NULL" ) );
        status = MQTTBadParameter;
    }
    else if( CHECK_SIZE_T_OVERFLOWS_16BIT( topicNameLength ) )
    {
        LogError( ( "topicNameLength must be fit in a 16-bit value (<65535)" ) );
        status = MQTTBadParameter;
    }
    else if( CHECK_SIZE_T_OVERFLOWS_16BIT( topicFilterLength ) )
    {
        LogError( ( "topicFilterLength must be fit in a 16-bit value (<65535)" ) );
        status = MQTTBadParameter;
    }
    else
    {
        /* Check for an exact match if the incoming topic name and the registered
         * topic filter length match. */
        if( topicNameLength == topicFilterLength )
        {
            matchStatus = strncmp( pTopicName, pTopicFilter, topicNameLength ) == 0;
        }

        if( matchStatus == false )
        {
            /* If an exact match was not found, match against wildcard characters in
             * topic filter. */

            /* Determine if topic filter starts with a wildcard. */
            topicFilterStartsWithWildcard = ( pTopicFilter[ 0 ] == '+' ) ||
                                            ( pTopicFilter[ 0 ] == '#' );

            /* Note: According to the MQTT 5.0 specification, incoming PUBLISH topic names
             * starting with "$" character cannot be matched against topic filter starting with
             * a wildcard, i.e. for example, "$SYS/sport" cannot be matched with "#" or
             * "+/sport" topic filters. */
            if( !( ( pTopicName[ 0 ] == '$' ) && ( topicFilterStartsWithWildcard == true ) ) )
            {
                matchStatus = matchTopicFilter( pTopicName, ( uint16_t ) topicNameLength, pTopicFilter, ( uint16_t ) topicFilterLength );
            }
        }

        /* Update the output parameter with the match result. */
        *pIsMatch = matchStatus;
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_GetSubAckStatusCodes( const MQTTPacketInfo_t * pSubackPacket,
                                        uint8_t ** pPayloadStart,
                                        size_t * pPayloadSize )
{
    MQTTStatus_t status = MQTTSuccess;
    uint32_t propertyLength = 0;

    if( pSubackPacket == NULL )
    {
        LogError( ( "Invalid parameter: pSubackPacket is NULL." ) );
        status = MQTTBadParameter;
    }
    else if( pPayloadStart == NULL )
    {
        LogError( ( "Invalid parameter: pPayloadStart is NULL." ) );
        status = MQTTBadParameter;
    }
    else if( pPayloadSize == NULL )
    {
        LogError( ( "Invalid parameter: pPayloadSize is NULL." ) );
        status = MQTTBadParameter;
    }
    else if( pSubackPacket->type != MQTT_PACKET_TYPE_SUBACK )
    {
        LogError( ( "Invalid parameter: Input packet is not a SUBACK packet: "
                    "ExpectedType=%02x, InputType=%02x",
                    ( int ) MQTT_PACKET_TYPE_SUBACK,
                    ( int ) pSubackPacket->type ) );
        status = MQTTBadParameter;
    }
    else if( pSubackPacket->pRemainingData == NULL )
    {
        LogError( ( "Invalid parameter: pSubackPacket->pRemainingData is NULL" ) );
        status = MQTTBadParameter;
    }

    /* A SUBACK must have a remaining length of at least 4 to accommodate the
     * packet identifier, atleast 1 byte for the property length and at least 1 return code. */
    else if( pSubackPacket->remainingLength < 4U )
    {
        LogError( ( "Invalid parameter: Packet remaining length is invalid: "
                    "Should be greater than or equal to 4 for SUBACK packet: InputRemainingLength=%lu",
                    ( unsigned long ) pSubackPacket->remainingLength ) );
        status = MQTTBadParameter;
    }
    else if( pSubackPacket->remainingLength >= MQTT_REMAINING_LENGTH_INVALID )
    {
        LogError( ( "Remaining length cannot be larger than MQTT maximum (268435456)." ) );
        status = MQTTBadParameter;
    }
    else
    {
        /* According to the MQTT 5.0 specification, the "Remaining Length" field represents the
         * combined length of the variable header and the payload. In a SUBACK packet, the variable
         * header consists of the Packet Identifier (2 bytes) followed by the properties.
         *
         * To locate the start of the payload:
         * - Skip the 2-byte Packet Identifier.
         * - Then skip the properties, whose total length is decoded using the
         *   decodeSubackPropertyLength() function.
         *
         * The payload starts immediately after the properties.
         * Its size is calculated by subtracting the size of the variable header
         * (2 bytes for Packet ID + property length) from the remaining length.
         */
        status = decodeSubackPropertyLength( &pSubackPacket->pRemainingData[ sizeof( uint16_t ) ],
                                             pSubackPacket->remainingLength,
                                             &propertyLength );

        if( status == MQTTSuccess )
        {
            *pPayloadStart = &pSubackPacket->pRemainingData[ sizeof( uint16_t ) + propertyLength ];
            *pPayloadSize = pSubackPacket->remainingLength - sizeof( uint16_t ) - propertyLength;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_GetUnsubAckStatusCodes( const MQTTPacketInfo_t * pUnsubackPacket,
                                          uint8_t ** pPayloadStart,
                                          size_t * pPayloadSize )
{
    MQTTStatus_t status = MQTTSuccess;
    uint32_t propertyLength = 0;

    if( pUnsubackPacket == NULL )
    {
        LogError( ( "Invalid parameter: pUnsubackPacket is NULL." ) );
        status = MQTTBadParameter;
    }
    else if( pPayloadStart == NULL )
    {
        LogError( ( "Invalid parameter: pPayloadStart is NULL." ) );
        status = MQTTBadParameter;
    }
    else if( pPayloadSize == NULL )
    {
        LogError( ( "Invalid parameter: pPayloadSize is NULL." ) );
        status = MQTTBadParameter;
    }
    else if( pUnsubackPacket->type != MQTT_PACKET_TYPE_UNSUBACK )
    {
        LogError( ( "Invalid parameter: Input packet is not an UNSUBACK packet: "
                    "ExpectedType=%02x, InputType=%02x",
                    ( int ) MQTT_PACKET_TYPE_UNSUBACK,
                    ( int ) pUnsubackPacket->type ) );
        status = MQTTBadParameter;
    }
    else if( pUnsubackPacket->pRemainingData == NULL )
    {
        LogError( ( "Invalid parameter: pUnsubackPacket->pRemainingData is NULL" ) );
        status = MQTTBadParameter;
    }
    else if( pUnsubackPacket->remainingLength < 4U )
    {
        LogError( ( "Invalid parameter: Packet remaining length is invalid: "
                    "Should be greater than or equal to 4 for UNSUBACK packet: InputRemainingLength=%lu",
                    ( unsigned long ) pUnsubackPacket->remainingLength ) );
        status = MQTTBadParameter;
    }
    else if( pUnsubackPacket->remainingLength >= MQTT_REMAINING_LENGTH_INVALID )
    {
        LogError( ( "Remaining length cannot be larger than MQTT maximum (268435456)." ) );
        status = MQTTBadParameter;
    }
    else
    {
        status = decodeSubackPropertyLength( &pUnsubackPacket->pRemainingData[ sizeof( uint16_t ) ],
                                             pUnsubackPacket->remainingLength,
                                             &propertyLength );

        if( status == MQTTSuccess )
        {
            *pPayloadStart = &pUnsubackPacket->pRemainingData[ sizeof( uint16_t ) + propertyLength ];
            *pPayloadSize = pUnsubackPacket->remainingLength - sizeof( uint16_t ) - propertyLength;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

const char * MQTT_Status_strerror( MQTTStatus_t status )
{
    const char * str = NULL;

    switch( status )
    {
        case MQTTSuccess:
            str = "MQTTSuccess";
            break;

        case MQTTBadParameter:
            str = "MQTTBadParameter";
            break;

        case MQTTNoMemory:
            str = "MQTTNoMemory";
            break;

        case MQTTSendFailed:
            str = "MQTTSendFailed";
            break;

        case MQTTRecvFailed:
            str = "MQTTRecvFailed";
            break;

        case MQTTBadResponse:
            str = "MQTTBadResponse";
            break;

        case MQTTServerRefused:
            str = "MQTTServerRefused";
            break;

        case MQTTNoDataAvailable:
            str = "MQTTNoDataAvailable";
            break;

        case MQTTIllegalState:
            str = "MQTTIllegalState";
            break;

        case MQTTStateCollision:
            str = "MQTTStateCollision";
            break;

        case MQTTKeepAliveTimeout:
            str = "MQTTKeepAliveTimeout";
            break;

        case MQTTNeedMoreBytes:
            str = "MQTTNeedMoreBytes";
            break;

        case MQTTStatusConnected:
            str = "MQTTStatusConnected";
            break;

        case MQTTStatusNotConnected:
            str = "MQTTStatusNotConnected";
            break;

        case MQTTStatusDisconnectPending:
            str = "MQTTStatusDisconnectPending";
            break;

        case MQTTPublishStoreFailed:
            str = "MQTTPublishStoreFailed";
            break;

        case MQTTPublishRetrieveFailed:
            str = "MQTTPublishRetrieveFailed";
            break;

        default:
            str = "Invalid MQTT Status code";
            break;
    }

    return str;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_GetBytesInMQTTVec( const MQTTVec_t * pVec,
                                     size_t * pOutput )
{
    size_t memoryRequired = 0;
    size_t i;
    const TransportOutVector_t * pTransportVec = pVec->pVector;
    size_t vecLen;
    MQTTStatus_t status = MQTTSuccess;

    assert( pVec != NULL );
    assert( pOutput != NULL );

    vecLen = pVec->vectorLen;

    for( i = 0; i < vecLen; i++ )
    {
        if( ADDITION_WILL_OVERFLOW_SIZE_T( memoryRequired, pTransportVec[ i ].iov_len ) )
        {
            LogError( ( "Adding all the vectors together will overflow size_t bounds!" ) );
            status = MQTTBadParameter;
            break;
        }

        memoryRequired += pTransportVec[ i ].iov_len;
    }

    if( status == MQTTSuccess )
    {
        *pOutput = memoryRequired;
    }

    return status;
}

/*-----------------------------------------------------------*/

void MQTT_SerializeMQTTVec( uint8_t * pAllocatedMem,
                            const MQTTVec_t * pVec )
{
    const TransportOutVector_t * pTransportVec;
    size_t vecLen;
    size_t index = 0;
    size_t i = 0;

    assert( pAllocatedMem != NULL );
    assert( pVec != NULL );

    pTransportVec = pVec->pVector;
    vecLen = pVec->vectorLen;

    for( i = 0; i < vecLen; i++ )
    {
        ( void ) memcpy( ( void * ) &pAllocatedMem[ index ], ( const void * ) pTransportVec[ i ].iov_base, pTransportVec[ i ].iov_len );
        index += pTransportVec[ i ].iov_len;
    }
}

/*-----------------------------------------------------------*/

const char * MQTT_GetPacketTypeString( uint8_t packetType )
{
    const char * retVal;

    if( ( packetType & 0xF0U ) == MQTT_PACKET_TYPE_PUBLISH )
    {
        retVal = "PUBLISH";
    }
    else
    {
        switch( packetType )
        {
            case MQTT_PACKET_TYPE_CONNECT:
                retVal = "CONNECT";
                break;

            case MQTT_PACKET_TYPE_CONNACK:
                retVal = "CONNACK";
                break;

            case MQTT_PACKET_TYPE_PUBACK:
                retVal = "PUBACK";
                break;

            case MQTT_PACKET_TYPE_PUBREC:
                retVal = "PUBREC";
                break;

            case MQTT_PACKET_TYPE_PUBREL:
                retVal = "PUBREL";
                break;

            case MQTT_PACKET_TYPE_PUBCOMP:
                retVal = "PUBCOMP";
                break;

            case MQTT_PACKET_TYPE_SUBSCRIBE:
                retVal = "SUBSCRIBE";
                break;

            case MQTT_PACKET_TYPE_SUBACK:
                retVal = "SUBACK";
                break;

            case MQTT_PACKET_TYPE_UNSUBSCRIBE:
                retVal = "UNSUBSCRIBE";
                break;

            case MQTT_PACKET_TYPE_UNSUBACK:
                retVal = "UNSUBACK";
                break;

            case MQTT_PACKET_TYPE_PINGREQ:
                retVal = "PINGREQ";
                break;

            case MQTT_PACKET_TYPE_PINGRESP:
                retVal = "PINGRESP";
                break;

            case MQTT_PACKET_TYPE_DISCONNECT:
                retVal = "DISCONNECT";
                break;

            case MQTT_PACKET_TYPE_AUTH:
                retVal = "AUTH";
                break;

            default:
                retVal = "UNKNOWN";
                break;
        }
    }

    return retVal;
}

// === test/cbmc/include/network_interface_stubs.h (CBMC include, verbatim from upstream) ===
/*
 * coreMQTT
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

/**
 * @file network_interface_stubs.h
 * @brief Stub definitions for the application defined transport interface send
 * and receive callback.
 */
#ifndef NETWORK_INTERFACE_STUBS_H_
#define NETWORK_INTERFACE_STUBS_H_

/* transport_interface.h must precede including this header. */

/**
 * @brief Application defined network interface receive function.
 *
 * @param[in] pNetworkContext Application defined network interface context.
 * @param[out] pBuffer MQTT network receive buffer.
 * @param[in] bytesToRecv MQTT requested bytes.
 *
 * @return Any value from INT32_MIN to INT32_MAX.
 */
int32_t NetworkInterfaceReceiveStub( NetworkContext_t * pNetworkContext,
                                     void * pBuffer,
                                     size_t bytesToRecv );

/**
 * @brief Application defined network interface send function.
 *
 * @param[in] pNetworkContext Application defined network interface context.
 * @param[out] pBuffer MQTT network send buffer.
 * @param[in] bytesToSend Number of bytes to send over the network.
 *
 * @return Any value from INT32_MIN to INT32_MAX.
 */
int32_t NetworkInterfaceSendStub( NetworkContext_t * pNetworkContext,
                                  const void * pBuffer,
                                  size_t bytesToSend );

#endif /* ifndef NETWORK_INTERFACE_STUBS_H_ */

// === test/cbmc/include/event_callback_stub.h (CBMC include, verbatim from upstream) ===
/*
 * coreMQTT
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

/**
 * @file event_callback_stub.h
 * @brief Stub definition for the application defined MQTT library incoming
 * event callback.
 */
#ifndef EVENT_CALLBACK_STUB_H_
#define EVENT_CALLBACK_STUB_H_

/* mqtt.h must precede including this header. */

/**
 * @brief User defined callback for receiving incoming publishes and incoming
 * acks.
 *
 * @param[in] pContext Initialized MQTT context.
 * @param[in] pPacketInfo Information on the type of incoming MQTT packet.
 * @param[in] pDeserializedInfo Deserialized information from incoming packet.
 */
bool EventCallbackStub( MQTTContext_t * pContext,
                        MQTTPacketInfo_t * pPacketInfo,
                        MQTTDeserializedInfo_t * pDeserializedInfo,
                        enum MQTTSuccessFailReasonCode * pReasonCode,
                        struct MqttPropBuilder * pSendPropsBuffer,
                        struct MqttPropBuilder * pGetPropsBuffer );

#endif /* ifndef EVENT_CALLBACK_STUB_H_ */

// === test/cbmc/include/get_time_stub.h (CBMC include, verbatim from upstream) ===
/*
 * coreMQTT
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

/**
 * @file get_time_stub.h
 * @brief Stub definition for the application defined callback to retrieve the
 * current time in milliseconds.
 */
#ifndef GET_TIME_STUB_H_
#define GET_TIME_STUB_H_

/**
 * Application defined callback to retrieve the current time in milliseconds.
 *
 * @return The current time in milliseconds.
 */
uint32_t GetCurrentTimeStub( void );

#endif /* ifndef GET_TIME_STUB_H_ */

// === test/cbmc/include/mqtt_cbmc_state.h (CBMC include, verbatim from upstream) ===
/*
 * coreMQTT
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

/**
 * @file mqtt_cbmc_state.h
 * @brief Allocation and assumption utilities for the MQTT library CBMC proofs.
 */
#ifndef MQTT_CBMC_STATE_H_
#define MQTT_CBMC_STATE_H_

#include <stdbool.h>

/* mqtt.h must precede including this header. */

#define IMPLIES( a, b )    ( !( a ) || ( b ) )

/**
 * @brief Allocate a #MQTTPacketInfo_t object.
 *
 * @param[in] pPacketInfo #MQTTPacketInfo_t object information.
 *
 * @return NULL or allocated #MQTTPacketInfo_t memory.
 */
MQTTPacketInfo_t * allocateMqttPacketInfo( MQTTPacketInfo_t * pPacketInfo );

/**
 * @brief Validate a #MQTTPacketInfo_t object.
 *
 * @param[in] pPacketInfo #MQTTPacketInfo_t object to validate.
 *
 * @return True if the #MQTTPacketInfo_t object is valid, false otherwise.
 *
 * @note A NULL object is a valid object. This is for coverage of the NULL
 * parameter checks in the function under proof.
 */
bool isValidMqttPacketInfo( const MQTTPacketInfo_t * pPacketInfo );

/**
 * @brief Allocate a #MQTTPublishInfo_t object.
 *
 * @param[in] pPublishInfo #MQTTPublishInfo_t object information.
 *
 * @return NULL or allocated #MQTTPublishInfo_t memory.
 */
MQTTPublishInfo_t * allocateMqttPublishInfo( MQTTPublishInfo_t * pPublishInfo );

/**
 * @brief Validate a #MQTTPublishInfo_t object.
 *
 * @param[in] pPublishInfo #MQTTPublishInfo_t object to validate.
 *
 * @return True if the #MQTTPublishInfo_t object is valid, false otherwise.
 *
 * @note A NULL object is a valid object. This is for coverage of the NULL
 * parameter checks in the function under proof.
 */
bool isValidMqttPublishInfo( const MQTTPublishInfo_t * pPublishInfo );

/**
 * @brief Allocate a #MQTTConnectInfo_t object.
 *
 * @param[in] pConnectInfo #MQTTConnectInfo_t object information.
 *
 * @return NULL or allocated #MQTTConnectInfo_t memory.
 */
MQTTConnectInfo_t * allocateMqttConnectInfo( MQTTConnectInfo_t * pConnectInfo );

/**
 * @brief Validate a #MQTTConnectInfo_t object.
 *
 * @param[in] pConnectInfo #MQTTConnectInfo_t object to validate.
 *
 * @return True if the #MQTTConnectInfo_t object is valid, false otherwise.
 *
 * @note A NULL object is a valid object. This is for coverage of the NULL
 * parameter checks in the function under proof.
 */
bool isValidMqttConnectInfo( const MQTTConnectInfo_t * pConnectInfo );

/**
 * @brief Allocate a #MQTTFixedBuffer_t object.
 *
 * @param[in] pBuffer #MQTTFixedBuffer_t object information.
 *
 * @return NULL or allocated #MQTTFixedBuffer_t memory.
 */
MQTTFixedBuffer_t * allocateMqttFixedBuffer( MQTTFixedBuffer_t * pFixedBuffer );

/**
 * @brief Validate a #MQTTFixedBuffer_t object.
 *
 * @param[in] pBuffer #MQTTFixedBuffer_t object to validate.
 *
 * @return True if the #MQTTFixedBuffer_t object is valid, false otherwise.
 *
 * @note A NULL object is a valid object. This is for coverage of the NULL
 * parameter checks in the function under proof.
 */
bool isValidMqttFixedBuffer( const MQTTFixedBuffer_t * pFixedBuffer );

MQTTPropBuilder_t * allocateMqttPropBuilder( MQTTPropBuilder_t * pPropBuilder );

bool isValidMqttPropBuilder( const MQTTPropBuilder_t * pPropBuilder );

/**
 * @brief Allocate an array of #MQTTSubscribeInfo_t objects.
 *
 * @param[in] pSubscriptionList #MQTTSubscribeInfo_t object information.
 * @param[in] subscriptionCount The amount of #MQTTSubscribeInfo_t objects to allocate.
 *
 * @return NULL or allocated #MQTTSubscribeInfo_t array.
 */
MQTTSubscribeInfo_t * allocateMqttSubscriptionList( MQTTSubscribeInfo_t * pSubscriptionList,
                                                    size_t subscriptionCount );

/**
 * @brief Validate an array of #MQTTSubscribeInfo_t objects.
 *
 * @param[in] pSubscriptionList #MQTTSubscribeInfo_t object information.
 * @param[in] subscriptionCount The length of #MQTTSubscribeInfo_t objects in the pSubscriptionList.
 *
 * @return True if the #MQTTSubscribeInfo_t is valid.
 *
 * @note A NULL object is a valid object. This is for coverage of the NULL
 * parameter checks in the function under proof.
 */
bool isValidMqttSubscriptionList( MQTTSubscribeInfo_t * pSubscriptionList,
                                  size_t subscriptionCount );

/**
 * @brief Allocate a #MQTTContext_t object.
 *
 * @param[in] pBuffer #MQTTContext_t object information.
 *
 * @return NULL or allocated #MQTTContext_t memory.
 */
MQTTContext_t * allocateMqttContext( MQTTContext_t * pContext );

/**
 * @brief Validate a #MQTTContext_t object.
 *
 * @param[in] pBuffer #MQTTContext_t object to validate.
 *
 * @return True if the #MQTTContext_t object is valid, false otherwise.
 *
 * @note A NULL object is a valid object. This is for coverage of the NULL
 * parameter checks in the function under proof.
 */
bool isValidMqttContext( const MQTTContext_t * pContext );

/**
 * @brief Allocate a #MQTTVec_t object.
 *
 * @param[in] mqttVec #MQTTVec_t object information.
 *
 * @return NULL or allocated #MQTTContext_t memory.
 */
MQTTVec_t * allocateMqttVec( MQTTVec_t * mqttVec );

#endif /* ifndef MQTT_CBMC_STATE_H_ */


// === Harness body, folded into main() ===
/*
 * coreMQTT
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

/**
 * @file MQTT_Init_harness.c
 * @brief Implements the proof harness for MQTT_Init function.
 */


int main(void) {
    MQTTContext_t * pContext;
    TransportInterface_t * pTransportInterface;
    MQTTGetCurrentTimeFunc_t getTimeFunction;
    MQTTEventCallback_t userCallback;
    MQTTFixedBuffer_t * pNetworkBuffer;

    pContext = malloc( sizeof( MQTTContext_t ) );
    pTransportInterface = malloc( sizeof( TransportInterface_t ) );
    getTimeFunction = malloc( sizeof( MQTTGetCurrentTimeFunc_t ) );
    userCallback = malloc( sizeof( MQTTEventCallback_t ) );
    pNetworkBuffer = malloc( sizeof( MQTTFixedBuffer_t ) );

    MQTT_Init( pContext,
               pTransportInterface,
               getTimeFunction,
               userCallback,
               pNetworkBuffer );
    return 0;
}
