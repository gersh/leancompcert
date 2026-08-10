import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk520A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk520A
