import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk983A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362486194815926858, 362486342031824914⟩, ⟨(-106884529257421771), (-97114259169947125)⟩, true⟩

def state01 : KState := ⟨⟨362483247808393872, 362483395055491511⟩, ⟨182784884170696811, 192558221332717499⟩, true⟩

def words00 : List Nat := [371285354106972505, 371285354102456623, 371285353984735919, 371285353968024681, 371285353959808086, 371285353963284632, 371285353902713749, 371285353822167797, 371285353740185024, 371285353739463973]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 98300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 98300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362479043452017032, 362479190730213103⟩, ⟨596147388892842949, 605923783504622285⟩, true⟩

def words01 : List Nat := [371285353767168532, 371285353816226245, 371285353863887428, 371285353867340306, 371285353776987704, 371285353691116628, 371285353616952463, 371285353620430680, 371285353561379350, 371285353502624664]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 98310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 98300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362485969453585173, 362486116762708032⟩, ⟨(-84784678791897778), (-75005243300096690)⟩, true⟩

def words02 : List Nat := [371285353483099891, 371285353490170424, 371285353599199966, 371285353709603707, 371285353799851126, 371285353803304527, 371285353826023208, 371285353892129302, 371285353968089323, 371285353979421987]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 98320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 98300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362486928399313221, 362487075739879493⟩, ⟨(-179060751107941778), (-169278223629301566)⟩, true⟩

def words03 : List Nat := [371285353992450714, 371285354006636205, 371285354112323334, 371285354168732430, 371285354250209908, 371285354333124536, 371285354414548050, 371285354418001767, 371285354378851279, 371285354400624968]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 98330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 98300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362480582299119466, 362480729670462862⟩, ⟨445036466175945263, 454822020436155417⟩, true⟩

def words04 : List Nat := [371285354505722719, 371285354509176701, 371285354476756160, 371285354420191614, 371285354362283640, 371285354306296426, 371285354200291409, 371285354199107890, 371285354196782802, 371285354195327490]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 98340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 98300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk983A
