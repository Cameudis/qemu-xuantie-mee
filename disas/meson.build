common_ss.add(when: 'CONFIG_ALPHA_DIS', if_true: files('alpha.c'))
common_ss.add(when: 'CONFIG_CRIS_DIS', if_true: files('cris.c'))
common_ss.add(when: 'CONFIG_HEXAGON_DIS', if_true: files('hexagon.c'))
common_ss.add(when: 'CONFIG_HPPA_DIS', if_true: files('hppa.c'))
common_ss.add(when: 'CONFIG_M68K_DIS', if_true: files('m68k.c'))
common_ss.add(when: 'CONFIG_MICROBLAZE_DIS', if_true: files('microblaze.c'))
common_ss.add(when: 'CONFIG_MIPS_DIS', if_true: files('mips.c', 'nanomips.c'))
common_ss.add(when: 'CONFIG_NIOS2_DIS', if_true: files('nios2.c'))
common_ss.add(when: 'CONFIG_RISCV_DIS', if_true: files(
    'riscv.c',
    'riscv-xthead.c',
    'riscv-xventana.c'
))
common_ss.add(when: 'CONFIG_SH4_DIS', if_true: files('sh4.c'))
common_ss.add(when: 'CONFIG_SPARC_DIS', if_true: files('sparc.c'))
common_ss.add(when: 'CONFIG_XTENSA_DIS', if_true: files('xtensa.c'))
common_ss.add(when: 'CONFIG_CSKY_DIS', if_true: files('csky.c'))
common_ss.add(when: capstone, if_true: [files('capstone.c'), capstone])
common_ss.add(files('disas.c'))

system_ss.add(files('disas-mon.c'))
specific_ss.add(capstone)
