import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk839A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360593087976983086, 360593133996241127⟩, ⟨(-897517127267503955), (-894909636014362337)⟩, true⟩

def state01 : KState := ⟨⟨360590726005014049, 360590772035752342⟩, ⟨(-699347332227627429), (-696738877723276771)⟩, true⟩

def words00 : List Nat := [360582467796265192, 360582467912526033, 360582468170436489, 360582468428699191, 360582468625261955, 360582468680230948, 360582468681313828, 360582468665028200, 360582468648521068, 360582468727750730]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 83900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 83900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360563822700970637, 360563868743050686⟩, ⟨1558322418099607830, 1560931824346660880⟩, true⟩

def words01 : List Nat := [360582468969562838, 360582469211603291, 360582469374462816, 360582469395680316, 360582469396692944, 360582469340017557, 360582469311054833, 360582469312259212, 360582469199678088, 360582468979279794]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 83910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 83900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360576955716733691, 360577001770203473⟩, ⟨456128882834749744, 458739244962589268⟩, true⟩

def words02 : List Nat := [360582468758613583, 360582468681381033, 360582468682373836, 360582468637043997, 360582468591633311, 360582468423882973, 360582468181333505, 360582467940592791, 360582467699500470, 360582467506471347]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 83920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 83900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360575590708105139, 360575636773025188⟩, ⟨570708821797452223, 573320145004885165⟩, true⟩

def words03 : List Nat := [360582467442422809, 360582467296053916, 360582467149457642, 360582467210767637, 360582467241735909, 360582467272900751, 360582467273993017, 360582467193708200, 360582466971498500, 360582466891502731]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 83930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 83900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360577238430260542, 360577284506527056⟩, ⟨432314426899961489, 434926702585464293⟩, true⟩

def words04 : List Nat := [360582466811119782, 360582466682969336, 360582466524161726, 360582466293691787, 360582466063009866, 360582465773698862, 360582465584551271, 360582465509799254, 360582465434916616, 360582465289166550]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 83940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 83900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk839A
