include "../../external//libraries/src/Collections/Sequences/LittleEndianNat.dfy"

abstract module {:options "-functionSyntax:4"} Default {
  import opened LittleEndianNat
  method TestZeroSeq()
  {
    reveal LittleEndianNat.ToNatRight();
    assert LittleEndianNat.ToNatRight([0, 0, 0]) == 0;
  }
}
