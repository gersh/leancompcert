import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk903A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk903B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk903A

def state06 : KState := ⟨⟨360590650768602261, 360590704454668017⟩, ⟨(-790065506977471500), (-786789677599199742)⟩, true⟩

def words05 : List Nat := [360581996327205268, 360581996330333821, 360581996455583883, 360581996686533792, 360581996845414864, 360581997004525427, 360581997102024550, 360581997103328847, 360581997174750776, 360581997272613822]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 90350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 90300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360583713888287901, 360583767586656310⟩, ⟨(-163262475910962820), (-159985534802945416)⟩, true⟩

def words06 : List Nat := [360581997469889021, 360581997545084785, 360581997546272840, 360581997519782737, 360581997493084471, 360581997372683294, 360581997313442890, 360581997312308907, 360581997311044740, 360581997267252929]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 90360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 90300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360604581231684874, 360604634942362946⟩, ⟨(-2049151883641782195), (-2045873830047533815)⟩, true⟩

def words07 : List Nat := [360581997410216142, 360581997553563397, 360581997818837062, 360581997994671505, 360581998065460838, 360581998136363756, 360581998204162918, 360581998333776612, 360581998585291535, 360581998837096933]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 90370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 90300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360578135309812920, 360578189032915934⟩, ⟨341083361980158980, 344362538600940788⟩, true⟩

def words08 : List Nat := [360581999018362159, 360581999077494424, 360581999143547104, 360581999210004116, 360581999245393647, 360581999246698913, 360581999204542764, 360581999068841135, 360581998932900161, 360581998774464789]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 90380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 90300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360563814648998507, 360563868384402325⟩, ⟨1635542123048762450, 1638822411600590364⟩, true⟩

def words09 : List Nat := [360581998733391208, 360581998654219317, 360581998574907929, 360581998421189591, 360581998145026526, 360581997818785489, 360581997492152236, 360581997288074058, 360581997150089115, 360581996950902332]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 90390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 90300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 90300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk903B
