/* 
 * File:   UxAS_ZeroMQ.h
 * Author: steve
 *
 * Created on December 13, 2013, 9:04 PM
 */

#ifndef UXAS_ZERO_MQ_H
#define	UXAS_ZERO_MQ_H

#include "zmq.hpp"

namespace n_ZMQ
{

    //TAKEN FROM zhelpers.cpp

    //  Receive 0MQ string from socket and convert into string
    std::string
    s_recv(zmq::socket_t & socket);

    //  Receive 0MQ string from socket save to a buffer
    size_t
    s_recv(zmq::socket_t & socket, void *buf_, size_t len_, int flags_ = 0);

    //  Convert string to 0MQ string and send to socket
    bool
    s_send(zmq::socket_t & socket, const std::string & string);

    //  Sends string as 0MQ string, as multipart non-terminal
    bool
    s_sendmore(zmq::socket_t & socket, const std::string & string);

    //  Sleep for a number of milliseconds
    void
    s_sleep(int msecs);

} //namespace n_ZMQ

#endif	/* UXAS_ZERO_MQ_H */
