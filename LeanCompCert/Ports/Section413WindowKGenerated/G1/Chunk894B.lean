import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk894A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk894B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk894A

def state06 : KState := ⟨⟨362484622910864173, 362484743956167305⟩, ⟨28330616133123182, 35642037953419946⟩, true⟩

def words05 : List Nat := [371285142292862697, 371285142318049105, 371285142371335963, 371285142374783559, 371285142413555573, 371285142454325069, 371285142493864085, 371285142496984026, 371285142369809288, 371285142369289968]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 89450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 89400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362477036294803719, 362477157367859342⟩, ⟨707085261648522838, 714399166351094770⟩, true⟩

def words06 : List Nat := [371285142476521605, 371285142479642975, 371285142446402304, 371285142390756275, 371285142333889027, 371285142301169271, 371285142225726351, 371285142203297048, 371285142179864196, 371285142157915798]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 89460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 89400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362497633908938538, 362497755010244584⟩, ⟨(-1135890843907379601), (-1128574411498167417)⟩, true⟩

def words07 : List Nat := [371285142070797751, 371285142037430101, 371285142081144434, 371285142098247013, 371285142100664553, 371285142098367905, 371285142213960475, 371285142275211141, 371285142418293233, 371285142562780898]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 89470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 89400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483595461243643, 362483716590727838⟩, ⟨120287746828248752, 127606700760881558⟩, true⟩

def words08 : List Nat := [371285142682402741, 371285142685523556, 371285142692026172, 371285142749275625, 371285142811722910, 371285142814844097, 371285142722453096, 371285142618534862, 371285142519674010, 371285142523242766]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 89480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 89400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362478455374484258, 362478576532031252⟩, ⟨580349030681485807, 587670496095195591⟩, true⟩

def words09 : List Nat := [371285142618239212, 371285142730425893, 371285142831569513, 371285142834693773, 371285142800207172, 371285142773601375, 371285142820462319, 371285142823584325, 371285142752708990, 371285142682825612]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 89490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 89400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 89400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk894B
