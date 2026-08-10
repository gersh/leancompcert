import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk240A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk240B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk240A

def state06 : KState := ⟨⟨360638191277529460, 360638194693091264⟩, ⟨(-1342794308251382978), (-1342738712148474672)⟩, true⟩

def words05 : List Nat := [360582356965684269, 360582360184800029, 360582364557625242, 360582370010268917, 360582374461043932, 360582378911499461, 360582382055725581, 360582384446325343, 360582386766211200, 360582389086003094]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 24050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 24000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360670197589543224, 360670201008055914⟩, ⟨(-2113075407686396683), (-2113019740570554403)⟩, true⟩

def words06 : List Nat := [360582393131314064, 360582396135643992, 360582398043668730, 360582399951567839, 360582401415826863, 360582404236018842, 360582408008938413, 360582411781606193, 360582414562339917, 360582418209644110]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 24060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 24000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360687509527358615, 360687512948835027⟩, ⟨(-2529928262875890439), (-2529872524408811419)⟩, true⟩

def words07 : List Nat := [360582423581044981, 360582428952092004, 360582433717172661, 360582436769384492, 360582438357901677, 360582439946309847, 360582443258397895, 360582447433717787, 360582451797159096, 360582456160312590]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 24070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 24000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360605015516644244, 360605018941107216⟩, ⟨(-543264037228664619), (-543208226830640447)⟩, true⟩

def words08 : List Nat := [360582459392864525, 360582460913719789, 360582464157648980, 360582467401403705, 360582470202311073, 360582471291857053, 360582471292141778, 360582470920474594, 360582470548780379, 360582470760175307]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 24080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 24000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360582493640279289, 360582497067694110⟩, ⟨(-331138799538716), (-275257276225312)⟩, true⟩

def words09 : List Nat := [360582473418524487, 360582476076713502, 360582477862027290, 360582479695503198, 360582480749600247, 360582481803692535, 360582484579182318, 360582485645151180, 360582485645905176, 360582485646704267]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 24090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 24000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 24000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk240B
