#include "hacllib.h"

// GCC builtin
/*
void memcpy(void *dest, void *src, uint64_t n) {
   // Typecast src and dest addresses to (char *)
   char *csrc = (char *)src;
   char *cdest = (char *)dest;

   // Copy contents of src[] to dest[]
   for (int i=0; i<n; i++)
       cdest[i] = csrc[i];
}

void* memset(void *b, int c, int len)
{
  int           i;
  unsigned char *p = b;
  i = 0;
  while(len > 0)
    {
      *p = c;
      p++;
      len--;
    }
  return(b);
} */

void KRML_CHECK_SIZE(uint64_t a, uint64_t b) {

}
