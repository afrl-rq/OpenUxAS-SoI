/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

#ifndef VMLINUX_H
#define VMLINUX_H

#if defined(CONFIG_PLAT_TK1)
#include "tk1_vmlinux.h"

#elif defined(CONFIG_PLAT_EXYNOS54XX)
#include "exynos5_vmlinux.h"

#else
#error "Unknown SoC"
#endif

#endif /* VMLINUX_H */

