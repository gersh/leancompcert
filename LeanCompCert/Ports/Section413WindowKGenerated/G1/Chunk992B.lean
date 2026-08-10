import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk992A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk992B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk992A

def state06 : KState := ⟨⟨362493957894471110, 362494108111398725⟩, ⟨(-878859742122490886), (-868793027661283950)⟩, true⟩

def words05 : List Nat := [371285355320814508, 371285355390997229, 371285355470945846, 371285355474434316, 371285355419356919, 371285355356202193, 371285355326168428, 371285355330013921, 371285355407185112, 371285355499318842]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 99250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 99200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362480677994924346, 362480828243363622⟩, ⟨439338882880158977, 449408725343990449⟩, true⟩

def words06 : List Nat := [371285355580530909, 371285355584022500, 371285355579023995, 371285355611631144, 371285355672994989, 371285355676483938, 371285355602772639, 371285355499470019, 371285355394756628, 371285355378705055]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 99260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 99200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362477024318472415, 362477174598337021⟩, ⟨802097548119846522, 812170510337186848⟩, true⟩

def words07 : List Nat := [371285355368466355, 371285355405282009, 371285355440799319, 371285355444350579, 371285355396301768, 371285355351818537, 371285355358452645, 371285355361941948, 371285355282220431, 371285355203799725]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 99270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 99200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362484520649164410, 362484670960295294⟩, ⟨57817619058004611, 67893685553014781⟩, true⟩

def words08 : List Nat := [371285355123819898, 371285355070896318, 371285354965807737, 371285354948507408, 371285354930151725, 371285354896961515, 371285354771697353, 371285354732214254, 371285354748459582, 371285354752072442]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 99280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 99200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362483412356330418, 362483562699210491⟩, ⟨167880429377287271, 177959648406214077⟩, true⟩

def words09 : List Nat := [371285354747797358, 371285354735890138, 371285354791237999, 371285354838387438, 371285354890347319, 371285354943654413, 371285354959775552, 371285354963265899, 371285354854442053, 371285354840684874]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 99290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 99200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 99200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk992B
