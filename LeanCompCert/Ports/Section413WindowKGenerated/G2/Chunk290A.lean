import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk290A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360668020180586048, 360668025224029065⟩, ⟨(-2467439879389801491), (-2467340961069747781)⟩, true⟩

def state01 : KState := ⟨⟨360617610180149846, 360617615227247193⟩, ⟨(-1005654050273644427), (-1005555025959663455)⟩, true⟩

def words00 : List Nat := [360582949441863583, 360582951077265039, 360582952435291139, 360582953793333699, 360582954849459984, 360582954849843371, 360582954725275137, 360582953711221830, 360582952868107927, 360582954063345237]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 29000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 29000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360578240950963621, 360578246001671566⟩, ⟨136718502444703546, 136817631520488086⟩, true⟩

def words01 : List Nat := [360582956067361653, 360582958071313140, 360582959351155020, 360582959854185522, 360582959854512090, 360582959532306967, 360582960072135798, 360582960761313833, 360582960761656496, 360582960599587503]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 29010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 29000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360640190989671696, 360640196044005432⟩, ⟨(-1661069134962202895), (-1660969900648306165)⟩, true⟩

def words02 : List Nat := [360582961459531795, 360582963392779281, 360582966510225021, 360582969627529254, 360582971707235750, 360582973260075419, 360582975996940376, 360582978733729125, 360582980408036603, 360582982379279853]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 29020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 29000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360637978173010501, 360637983230997245⟩, ⟨(-1596760593189525864), (-1596661252810523408)⟩, true⟩

def words03 : List Nat := [360582983756801937, 360582985134271829, 360582987695251028, 360582990848303293, 360582993699648066, 360582996550866646, 360582998808789164, 360582999888781175, 360583001782457552, 360583003676133070]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 29030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 29000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360653298239669243, 360653303301274142⟩, ⟨(-2041801743494087635), (-2041702298026033433)⟩, true⟩

def words04 : List Nat := [360583006477203644, 360583008933212585, 360583010483602880, 360583012033919363, 360583012975494049, 360583014641122308, 360583017000737886, 360583019360264139, 360583020949818705, 360583023369498092]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 29040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 29000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk290A
