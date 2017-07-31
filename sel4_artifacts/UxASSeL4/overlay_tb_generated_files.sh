#!/bin/bash


rm -r ./make_template
cp -r ./tb/soi_tk1/make_template ./

rm -r ./include
cp -r ./tb/soi_tk1/include ./

rm -r ./interfaces/*
for i in MissionSoftware__mission_command_impl_writer.idl4\
         bool_writer.idl4\
         tb_Monitor_bool_1.idl4\
         SMACCM_DATA__UART_Packet_i_writer.idl4\
         tb_Monitor_SMACCM_DATA__UART_Packet_i_23388.idl4\
         uint32_t_writer.idl4\
         tb_Monitor_uint32_t_1.idl4;
do
   cp ./tb/soi_tk1/interfaces/$i ./interfaces
done

rm -r ./components/tb_Monitors/*
for i in tb_Asset_Waypoint_Manager_in_uart_packet_Monitor\
         tb_UART_Driver_in_uart_packet_Monitor\
         tb_Virtual_Machine_waypoint_write_Monitor\
         tb_Waypoint_Manager_mission_write_Monitor\
         tb_Asset_Waypoint_Manager_waypoint_read_vm_Monitor\
         tb_Asset_Waypoint_Manager_waypoint_read_wm_Monitor\
         tb_Virtual_Machine_mission_read_Monitor\
         tb_Waypoint_Manager_in_send_success_Monitor\
         tb_Waypoint_Manager_waypoint_write_Monitor;
do
   cp -r ./tb/soi_tk1/components/tb_Monitors/$i ./components/tb_Monitors/
done


for i in Asset_Waypoint_Manager\
         Waypoint_Manager;
do
   rsync -ravz -u --existing ./tb/soi_tk1/components/$i ./components/
done

for i in Asset_Waypoint_Manager\
         Waypoint_Manager\
         Clock_Driver\
         UART_Driver\
         Virtual_Machine;
do
   cp -r ./tb/soi_tk1/components/$i/include/tb_$i.h ./components/$i/include/
done

perl -pe 's/\/\/ADDITIONAL_CONFIGS/

        Virtual_Machine_inst.base_prio = 100;
        Virtual_Machine_inst.priority = 101;

        Virtual_Machine_inst.untyped_mmios = [ 
            "0x50046000:12", \/\/ Interrupt Controller Virtual CPU interface (Virtual Machine view)
            "0x60004000:12", \/\/ Interrupt controller registers (ICTLR)
            "0x700b0000:12", \/\/ SDMMC-1, SDMMC-2, SDMMC-3, SDMMC-4,
            "0x7d000000:12", \/\/ USB on-the-go (micro)
            "0x7d004000:12", \/\/ USB on top board
            "0x7d008000:12", \/\/ USB on bottom board
            "0xb0000000:28", \/\/ Linux kernel memory regions
            "0xc0000000:29", \/\/ Linux kernel memory regions
            "0xe0000000:28", \/\/ Linux kernel memory regions
            ];

        Virtual_Machine_inst.irqs =  [
            27, \/\/ INTERRUPT_VGPT (INTERRUPT_PPI_11)
            53, \/\/ INTERRUPT_USB2
            63, \/\/ INTERRUPT_SDMMC4
            122, \/\/ INTERRUPT_UARTD
            129, \/\/ INTERRUPT_USB3
            ];

        Virtual_Machine_inst.smmu = [10, 23];

        Virtual_Machine_inst.asid_pool = true;

        Virtual_Machine_inst.simple = true;
        Virtual_Machine_inst.cnode_size_bits = 21;
        Virtual_Machine_inst.simple_untyped24_pool = 10;/' ./tb/soi_tk1/soi_tk1_assembly.camkes > ./soi_tk1_assembly.camkes  

