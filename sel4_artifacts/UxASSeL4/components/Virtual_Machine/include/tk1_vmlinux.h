/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

#ifndef VMLINUX_TK1_H
#define VMLINUX_TK1_H

#include <sel4arm-vmm/vm.h>

#define VUSB_ADDRESS         0x33330000
#define VUSB_IRQ             198
#define VUSB_NINDEX          5
#define VUSB_NBADGE          0x123

#define INTERRUPT_VTIMER                27
#define INTERRUPT_TMR1                  32
#define INTERRUPT_TMR2                  33
#define INTERRUPT_RTC                   34
#define INTERRUPT_CEC                   35
#define INTERRUPT_SHR_SEM_INBOX_FULL    36
#define INTERRUPT_SHR_SEM_INBOX_EMPTY   37
#define INTERRUPT_SHR_SEM_OUTBOX_FULL   38
#define INTERRUPT_SHR_SEM_OUTBOX_EMPTY  39
#define INTERRUPT_VDE_UCQ               40
#define INTERRUPT_VDE_SYNC_TOKEN        41
#define INTERRUPT_VDE_BSEV              42
#define INTERRUPT_VDE_BSEA              43
#define INTERRUPT_VDE_SXE               44
#define INTERRUPT_SATA_RX_STAT          45
#define INTERRUPT_SDMMC1                46
#define INTERRUPT_SDMMC2                47
#define INTERRUPT_VDE                   49
#define INTERRUPT_AVP_UCQ               50
#define INTERRUPT_SDMMC3                51
#define INTERRUPT_USB                   52
#define INTERRUPT_USB2                  53
#define INTERRUPT_SATA_CTL              55
#define INTERRUPT_VCP                   57
#define INTERRUPT_APB_DMA_CPU           58
#define INTERRUPT_AHB_DMA_CPU           59
#define INTERRUPT_ARB_SEM_GNT_COP       60
#define INTERRUPT_ARB_SEM_GNT_CPU       61
#define INTERRUPT_OWR                   62
#define INTERRUPT_SDMMC4                63
#define INTERRUPT_GPIO1                 64
#define INTERRUPT_GPIO2                 65
#define INTERRUPT_GPIO3                 66
#define INTERRUPT_GPIO4                 67
#define INTERRUPT_UARTA                 68
#define INTERRUPT_UARTB                 69
#define INTERRUPT_I2C                   70
#define INTERRUPT_USB3_HOST             71
#define INTERRUPT_USB3_HOST_SMI         72
#define INTERRUPT_TMR3                  73
#define INTERRUPT_TMR4                  74
#define INTERRUPT_USB3_HOST_PME         75
#define INTERRUPT_USB3_DEV_HOST         76
#define INTERRUPT_ACTMON                77
#define INTERRUPT_UARTC                 78
#define INTERRUPT_HSI                   79
#define INTERRUPT_THERMAL               80
#define INTERRUPT_XUSB_PADCTL           81
#define INTERRUPT_TSEC                  82
#define INTERRUPT_EDP                   83
#define INTERRUPT_VFIR                  84
#define INTERRUPT_I2C5                  85
#define INTERRUPT_STAT_MON              86
#define INTERRUPT_GPIO5                 87
#define INTERRUPT_USB3_DEV_SMI          88
#define INTERRUPT_USB3_DEV_PME          89
#define INTERRUPT_SE                    90
#define INTERRUPT_SPI1                  91
#define INTERRUPT_APB_DMA_COP           92
#define INTERRUPT_AHB_DMA_COP           93
#define INTERRUPT_CLDVFS                94
#define INTERRUPT_I2C6                  95
#define INTERRUPT_HOST1X_SYNCPT_COP     96
#define INTERRUPT_HOST1X_SYNCPT_CPU     97
#define INTERRUPT_HOST1X_GEN_COP        98
#define INTERRUPT_HOST1X_GEN_CPU        99
#define INTERRUPT_MSENC                 100
#define INTERRUPT_VI                    101
#define INTERRUPT_ISPB                  102
#define INTERRUPT_ISP                   103
#define INTERRUPT_VIC                   104
#define INTERRUPT_DISPLAY               105
#define INTERRUPT_DISPLAYB              106
#define INTERRUPT_HDMI                  107
#define INTERRUPT_SOR                   108
//#define INTERRUPT_MC                  109
#define INTERRUPT_EMC                   110
#define INTERRUPT_SPI6                  111
#define INTERRUPT_HDA                   113
#define INTERRUPT_SPI2                  114
#define INTERRUPT_SPI3                  115
#define INTERRUPT_I2C2                  116
#define INTERRUPT_PMU_EXT               118
#define INTERRUPT_GPIO6                 119
#define INTERRUPT_GPIO7                 121
#define INTERRUPT_UARTD                 122
#define INTERRUPT_I2C3                  124
#define INTERRUPT_SW                    127
#define INTERRUPT_SNOR                  128
#define INTERRUPT_USB3                  129
#define INTERRUPT_PCIE_INT              130
#define INTERRUPT_PCIE_MSI              131
#define INTERRUPT_PCIE_WAKE             132
#define INTERRUPT_AVP_CACHE             133
#define INTERRUPT_AUDIO_CLUSTER         135
#define INTERRUPT_APB_DMA_CH0           136
#define INTERRUPT_APB_DMA_CH1           137
#define INTERRUPT_APB_DMA_CH2           138
#define INTERRUPT_APB_DMA_CH3           139
#define INTERRUPT_APB_DMA_CH4           140
#define INTERRUPT_APB_DMA_CH5           141
#define INTERRUPT_APB_DMA_CH6           142
#define INTERRUPT_APB_DMA_CH7           143
#define INTERRUPT_APB_DMA_CH8           144
#define INTERRUPT_APB_DMA_CH9           145
#define INTERRUPT_APB_DMA_CH10          146
#define INTERRUPT_APB_DMA_CH11          147
#define INTERRUPT_APB_DMA_CH12          148
#define INTERRUPT_APB_DMA_CH13          149
#define INTERRUPT_APB_DMA_CH14          150
#define INTERRUPT_APB_DMA_CH15          151
#define INTERRUPT_I2C4                  152
#define INTERRUPT_TMR5                  153
#define INTERRUPT_HIER_GROUP1_COP       154
#define INTERRUPT_WDT_CPU               155
#define INTERRUPT_WDT_AVP               156
#define INTERRUPT_GPIO8                 157
#define INTERRUPT_CAR                   158
#define INTERRUPT_HIER_GROUP1_CPU       159
#define INTERRUPT_APB_DMA_CH16          160
#define INTERRUPT_APB_DMA_CH17          161
#define INTERRUPT_APB_DMA_CH18          162
#define INTERRUPT_APB_DMA_CH19          163
#define INTERRUPT_APB_DMA_CH20          164
#define INTERRUPT_APB_DMA_CH21          165
#define INTERRUPT_APB_DMA_CH22          166
#define INTERRUPT_APB_DMA_CH23          167
#define INTERRUPT_APB_DMA_CH24          168
#define INTERRUPT_APB_DMA_CH25          169
#define INTERRUPT_APB_DMA_CH26          170
#define INTERRUPT_APB_DMA_CH27          171
#define INTERRUPT_APB_DMA_CH28          172
#define INTERRUPT_APB_DMA_CH29          173
#define INTERRUPT_APB_DMA_CH30          174
#define INTERRUPT_APB_DMA_CH31          175
#define INTERRUPT_CPU0_PMU              176
#define INTERRUPT_CPU1_PMU              177
#define INTERRUPT_CPU2_PMU              178
#define INTERRUPT_CPU3_PMU              179
#define INTERRUPT_SDMMC1_SYS            180
#define INTERRUPT_SDMMC2_SYS            181
#define INTERRUPT_SDMMC3_SYS            182
#define INTERRUPT_SDMMC4_SYS            183
#define INTERRUPT_TMR6                  184
#define INTERRUPT_TMR7                  185
#define INTERRUPT_TMR8                  186
#define INTERRUPT_TMR9                  187
#define INTERRUPT_TMR0                  188
#define INTERRUPT_GPU                   189
#define INTERRUPT_GPU_NONSTALL          190
#define ARDPAUX                         191


#define LINUX_RAM_PADDR_BASE 0xb0000000
#define LINUX_RAM_BASE    0x80000000
#define LINUX_RAM_SIZE    0x40000000
#define PLAT_RAM_END      0xffffffff
/* the offset between actual physcial memory and guest physical memory */
#define LINUX_RAM_OFFSET  (LINUX_RAM_PADDR_BASE - LINUX_RAM_BASE)


int load_linux(vm_t* vm, const char* kernel_name, const char* dtb_name);

void vusb_notify(void);

#endif /* VMLINUX_H */

