
#include <stdint.h>

// -----------------------------------------------------------------------------

uint64_t c_dual_nibble(uint64_t word)
{
  uint64_t n    = (word & 15);    // length
  uint64_t h    = (word >> 60);   // height
  uint64_t dual = h;              // length of dual = height of original
  uint64_t w    = word - n;       // zero out the low nibble

  uint64_t o = 60;
  for(uint64_t i=0; i<n; i++)
  { uint64_t k = ( (w >> (64-4*(n-i))) 
                 - (w >> (60-4*(n-i))) ) & 15 ;   // diff
    for(uint64_t j=0;j<k;j++) { dual |= (n-i) << o ; o -= 4 ; } 
  }

  return dual;
}

// -----------------------------------------------------------------------------

