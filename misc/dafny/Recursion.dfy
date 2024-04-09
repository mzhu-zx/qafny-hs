function CastHadEn_Phase_(p : seq<nat>) : (p' : seq<nat>)
  decreases |p|
{
  if |p| == 0 then
    []
  else
    var p'' := CastHadEn_Phase_(p[1..]);
    var now := p[0];
    p'' + seq(|p''|, i requires 0 <= i < |p''| => now + p''[i])
}
