import zmq, sqlite3, glob, sys, os
from lmcp import LMCPFactory
from pathlib import Path
import argparse

# parse all arguments
parser = argparse.ArgumentParser(description='Convert UxAS text logs to sqlite logs')
parser.add_argument('logdir', help='directory of text logs')
parser.add_argument('-o', '--output', type=str, help='output database file name')
args = parser.parse_args()

# ensure path to log directory is valid
procpath=Path(args.logdir)
if not procpath.exists():
    print(procpath, "does not exist!")
    sys.exit()
if not procpath.is_dir():
    print(procpath, "is not a directory!")
    sys.exit()

# prepare LMCP factory
factory = LMCPFactory.LMCPFactory();

# open database, removing if necessary
try:
    os.remove(args.output)
except OSError:
    pass
conn=sqlite3.connect(args.output)
db=conn.cursor()
db.execute('''CREATE TABLE msg (
            id INTEGER PRIMARY KEY,
            time_ms INTEGER NOT NULL,
            descriptor TEXT NOT NULL,
            groupID TEXT NOT NULL,
            entityID INTEGER NOT NULL,
            serviceID INTEGER NOT NULL,
            xml BLOB NOT NULL)''')

# process all the log files in 'logdir'
for xmlFile in sorted(procpath.glob("*")):
    print('loading [', xmlFile, ']')
    contents = xmlFile.read_text()
    for msg in contents.split('<MessageData UtcTimeSinceEpoch_ms="'):
        if len(msg.split('" ThreadId="')) > 1:
            utctime, remainder = msg.split('" ThreadId="')
            junk, header_and_body = remainder.split("<!-- lmcp|")
            header, msgbody = header_and_body.split(" -->")
            msg_desc, msg_group, entityid, serviceid = header.split('|')
        
            db.execute("INSERT INTO msg VALUES (NULL,'"+utctime+"','"+msg_desc+"','"+msg_group+"','"+entityid+"','"+serviceid+"','"+msgbody.strip()+"')")

# commit and close the database
conn.commit()
conn.close()

