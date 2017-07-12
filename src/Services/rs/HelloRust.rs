// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
//
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/*
 * File:   HelloRust.rs
 * Author: acfoltzer
 */

extern crate lmcp_rs;
use lmcp_rs::*;

use std::slice;

#[no_mangle]
pub extern "C" fn processReceivedLmcpMessage_rs(buf: *const u8, len: usize) {
    let buf_slice = unsafe {
        slice::from_raw_parts(buf, len)
    };
    println!("Hello, Rust!");
    println!("Got {} bytes!", buf_slice.len());
    println!("Raw bytes: {:?}", buf_slice);
    let msg = lmcp_msg_deser(buf_slice).unwrap().unwrap();
    println!("msg={:?}", msg);
    if let LmcpType::KeyValuePair(kv) = msg {
        let k = String::from_utf8(kv.key).unwrap();
        let v = String::from_utf8(kv.value).unwrap();
        println!("key= {}, value = {}", k, v);
    }
}
