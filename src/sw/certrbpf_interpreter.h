/**************************************************************************/
/*  This file is part of CertrBPF,                                        */
/*  a formally verified rBPF verifier + interpreter + JIT in Coq.         */
/*                                                                        */
/*  Copyright (C) 2022 Inria                                              */
/*                                                                        */
/*  This program is free software; you can redistribute it and/or modify  */
/*  it under the terms of the GNU General Public License as published by  */
/*  the Free Software Foundation; either version 2 of the License, or     */
/*  (at your option) any later version.                                   */
/*                                                                        */
/*  This program is distributed in the hope that it will be useful,       */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of        */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         */
/*  GNU General Public License for more details.                          */
/*                                                                        */
/**************************************************************************/

#ifndef CERTRBPF_INTERPRETER_H
#define	CERTRBPF_INTERPRETER_H

#include <stdio.h>

/*
defining bpf_flag
 */

enum BPF_FLAG {
    vBPF_SUCC_RETURN         = 1,
    vBPF_OK                  = 0,
    vBPF_ILLEGAL_INSTRUCTION = -1,
    vBPF_ILLEGAL_MEM         = -2,
    vBPF_ILLEGAL_JUMP        = -3,
    vBPF_ILLEGAL_CALL        = -4,
    vBPF_ILLEGAL_LEN         = -5,
    vBPF_ILLEGAL_REGISTER    = -6,
    vBPF_NO_RETURN           = -7,
    vBPF_OUT_OF_BRANCHES     = -8,
    vBPF_ILLEGAL_DIV         = -9,
};

/*
defining bpf_permission
 */

enum BPF_PERM {
    Freeable = 3,
    Writable = 2,
    Readable = 1,
    Nonempty = 0,
};

struct memory_region {
  unsigned int start_addr;
  unsigned int block_size;
  unsigned int block_perm;
  unsigned char* block_ptr;
};

struct bpf_state {
  unsigned int state_pc;
  int bpf_flag;
  unsigned long long regsmap[11];
  unsigned int ins_len;
  const unsigned long long * ins;
  unsigned int mrs_num;
  struct memory_region *mrs;
};

unsigned long long bpf_interpreter(struct bpf_state *, unsigned int);

#endif /* CERTRBPF_INTERPRETER_H */
