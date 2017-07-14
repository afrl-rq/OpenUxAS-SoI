# How to add a new message

Each message used by UxAS must be defined in an XML document (MDM). MDMs for all relevant messages are then used
by `LmcpGen` to create a C++ library that allows easy access to the data fields of each message. As new functionality
often depends on new information in the system, the ability to quickly update the message set and corresponding C++
libary is crucial to exanding UxAS capability. The following is a set of steps for adding a new message to UxAS:

1. Copy an exisiting MDM file
1. Rename MDM file to a unique 8 character string (e.g. NEWMDM.xml)
1. Update the top-level comment to describe your new set of messages
1. Change the `SeriesName` to the same name as the file (e.g. `<SeriesName>NEWMDM</SeriesName>`)
1. Change the namespace to reflect your new MDM (e.g. `<Namespace>uxas/projects/newmdm</Namespace>`)
1. Change the version number to 1 (e.g. `<Version>1</Version>`)
1. Remove all copied messages from between the `<StructList>` tags
1. Add new messages following Section 8 of `src/doc/lmcp.html` in the `LmcpGen` project
1. In the root of `OpenUxAS`, run the script `RunLmcpGen.sh`
1. Rebuild (e.g. `ninja -C build uxas`)
