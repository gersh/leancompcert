import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk881

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360599131328078688, 360599182262130230⟩, ⟨(-1500605301406041195), (-1497575048208147307)⟩, true⟩

def state01 : KState := ⟨⟨360586812083388250, 360586863029556463⟩, ⟨(-415240368465281128), (-412209047733096794)⟩, true⟩

def words00 : List Nat := [360582183983894648, 360582184152363860, 360582184377187998, 360582184602377709, 360582184774549475, 360582184818219998, 360582184819351209, 360582184788218338, 360582184756861285, 360582184736860511]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 88100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 88100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360567666794347313, 360567717752459302⟩, ⟨1271761537828107958, 1274793910987908628⟩, true⟩

def words01 : List Nat := [360582184790036235, 360582184843451037, 360582184844583595, 360582184815320388, 360582184748819806, 360582184650321429, 360582184580154511, 360582184581423990, 360582184482621702, 360582184319765112]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 88110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 88100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360579811084343290, 360579862054458614⟩, ⟨201489853935116579, 204523284888362367⟩, true⟩

def words02 : List Nat := [360582184156631180, 360582184013750324, 360582183948655452, 360582183880761410, 360582183812772044, 360582183633439234, 360582183352545547, 360582183110443930, 360582182867956500, 360582182754389267]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 88120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 88100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360574824879743412, 360574875861943900⟩, ⟨640952499925434890, 643986996003454236⟩, true⟩

def words03 : List Nat := [360582182729188960, 360582182624288687, 360582182519139608, 360582182549595404, 360582182574824058, 360582182600261214, 360582182601422903, 360582182525757314, 360582182353595846, 360582182272154968]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 88130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 88100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360569846359176693, 360569897353329942⟩, ⟨1079714764938809063, 1082750314592276331⟩, true⟩

def words04 : List Nat := [360582182190288959, 360582182165295972, 360582182011566138, 360582181759981541, 360582181508176412, 360582181170118749, 360582180911232284, 360582180761385688, 360582180611403968, 360582180397171035]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 88140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 88100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360584928827964312, 360584979834121974⟩, ⟨(-249947086569451997), (-246910478667223303)⟩, true⟩

def words05 : List Nat := [360582180258874780, 360582180110483345, 360582179961727153, 360582179851644354, 360582179722058293, 360582179484591638, 360582179246886988, 360582179120290396, 360582179124106966, 360582179157193772]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 88150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 88100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360585974899323647, 360586025917569294⟩, ⟨(-342269189785567797), (-339231516146694371)⟩, true⟩

def words06 : List Nat := [360582179158325168, 360582179126958067, 360582179081881167, 360582179112257820, 360582179113346535, 360582179022616209, 360582178894691580, 360582178702521842, 360582178510112860, 360582178490227576]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 88160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 88100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360560835078707648, 360560886108934391⟩, ⟨1874484875255872576, 1877523605326558518⟩, true⟩

def words07 : List Nat := [360582178610143018, 360582178730321475, 360582178765142647, 360582178766412856, 360582178672644756, 360582178545803059, 360582178418773502, 360582178420043723, 360582178292893795, 360582178052746215]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 88170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 88100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360588424891511556, 360588475933721561⟩, ⟨(-558488400315191082), (-555448613500211670)⟩, true⟩

def words08 : List Nat := [360582177812315911, 360582177676419465, 360582177684743602, 360582177740215691, 360582177741387436, 360582177687772534, 360582177637266644, 360582177607038751, 360582177614983639, 360582177687715731]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 88180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 88100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360585045077460448, 360585096131806853⟩, ⟨(-260468379868631677), (-257427522687375859)⟩, true⟩

def words09 : List Nat := [360582177688858831, 360582177678161064, 360582177667232021, 360582177645551758, 360582177646615886, 360582177613038675, 360582177579320199, 360582177481419998, 360582177450920423, 360582177485502533]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 88190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 88100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 88100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk881
