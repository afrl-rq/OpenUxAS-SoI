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

    static std::string
    s_recv(zmq::socket_t & socket) {

        zmq::message_t message;
        socket.recv(&message);

        return std::string(static_cast<char*> (message.data()), message.size());
    }

    //  Receive 0MQ string from socket save to a buffer

    static size_t
    s_recv(zmq::socket_t & socket,void *buf_, size_t len_, int flags_ = 0)
   {
        int nbytes = socket.recv(buf_, len_, flags_);
        return(nbytes);
    }

    //  Convert string to 0MQ string and send to socket

    static bool
    s_send(zmq::socket_t & socket, const std::string & string) {

        zmq::message_t message(string.size());
        memcpy(message.data(), string.data(), string.size());

        bool rc = socket.send(message);
        return (rc);
    }

    //  Sends string as 0MQ string, as multipart non-terminal

    static bool
    s_sendmore(zmq::socket_t & socket, const std::string & string) {

        zmq::message_t message(string.size());
        memcpy(message.data(), string.data(), string.size());

        bool rc = socket.send(message, ZMQ_SNDMORE);
        return (rc);
    }

    //  Sleep for a number of milliseconds

    static void
    s_sleep(int msecs) {
#ifdef _WIN32
        Sleep(msecs);
#else
        struct timespec t;
        t.tv_sec = msecs / 1000;
        t.tv_nsec = (msecs % 1000) * 1000000;
        nanosleep(&t, NULL);
#endif
    }

} //namespace n_ZMQ



#endif	/* UXAS_ZERO_MQ_H */

