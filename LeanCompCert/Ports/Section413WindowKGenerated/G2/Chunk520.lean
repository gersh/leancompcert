import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk520

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360575624272573135, 360575641290157105⟩, ⟨329804278273138664, 330402200017120654⟩, true⟩

def state01 : KState := ⟨⟨360596547036626096, 360596564061014398⟩, ⟨(-758379853975035141), (-757781578372313855)⟩, true⟩

def words00 : List Nat := [360581995214407435, 360581995568854171, 360581995626460745, 360581995684189315, 360581995684853178, 360581995425822949, 360581994797614241, 360581994455532183, 360581994139503028, 360581994420392755]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 52000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 52000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360570478781924186, 360570495813172031⟩, ⟨597593730317062582, 598192362718779514⟩, true⟩

def words01 : List Nat := [360581994515321295, 360581994610318911, 360581994813911833, 360581995204797033, 360581995425871711, 360581995647055384, 360581995647708025, 360581995586356576, 360581995309884517, 360581995089656437]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 52010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 52000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360608910072372354, 360608927110403918⟩, ⟨(-1401818790105208456), (-1401219804781607574)⟩, true⟩

def words02 : List Nat := [360581995017095101, 360581995120461576, 360581995121103188, 360581995039291430, 360581994957353543, 360581994896268724, 360581995384321319, 360581995872493191, 360581996112059691, 360581996630405810]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 52020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 52000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360613989998602984, 360614007043438403⟩, ⟨(-1666231092781226431), (-1665631753419271565)⟩, true⟩

def words03 : List Nat := [360581997138147338, 360581997646070571, 360581998408605166, 360581998802612904, 360581998880474304, 360581998958388988, 360581999160691512, 360581999667764755, 360582000283403294, 360582000899178699]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 52030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 52000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360574007651749380, 360574024703439143⟩, ⟨414504046927592981, 415103743023756957⟩, true⟩

def words04 : List Nat := [360582001214445656, 360582001215166245, 360582001369087533, 360582001577155330, 360582001577768814, 360582001530710103, 360582001235923621, 360582000755852919, 360582000275664018, 360581999799366593]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 52040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 52000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360550228355898145, 360550245414387815⟩, ⟨1652477214952313026, 1653077265016516972⟩, true⟩

def words05 : List Nat := [360581999862019148, 360582000078039284, 360582000109003319, 360582000109726002, 360582000020587678, 360581999756541693, 360581999595886550, 360581999596607361, 360581999332559291, 360581998723358552]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 52050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 52000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360609369482377257, 360609386547666157⟩, ⟨(-1426778673410858864), (-1426178269344487734)⟩, true⟩

def words06 : List Nat := [360581998114016407, 360581997780623718, 360581997633627321, 360581997542940139, 360581997452209653, 360581997041278104, 360581996640878230, 360581996608969863, 360581996912401720, 360581997439153848]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 52060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 52000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360593980894847434, 360593997967016784⟩, ⟨(-625465934137025064), (-624865171772474572)⟩, true⟩

def words07 : List Nat := [360581997708493976, 360581997977901821, 360581998145084101, 360581998599963694, 360581998957364463, 360581999314868698, 360581999487486924, 360581999556029707, 360581999786998196, 360582000018210646]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 52070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 52000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360573894319856806, 360573911398809054⟩, ⟨420756470723978630, 421357586377054264⟩, true⟩

def words08 : List Nat := [360582000617253256, 360582000848473594, 360582000892642966, 360582000936883390, 360582000937490977, 360582000739158000, 360582000726907452, 360582000702690882, 360582000678394676, 360582000429071620]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 52080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 52000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360617608255005664, 360617625340766727⟩, ⟨(-1856577186311588019), (-1855975715953280679)⟩, true⟩

def words09 : List Nat := [360582000274371014, 360582000228622941, 360582000433714102, 360582000747383900, 360582000748050017, 360582000713339006, 360582000888009463, 360582001321393986, 360582002005739791, 360582002690223489]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 52090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 52000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 52000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk520
