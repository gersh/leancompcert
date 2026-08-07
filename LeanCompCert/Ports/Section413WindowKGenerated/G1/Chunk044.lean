import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk044

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362838720084292162, 362838720309495224⟩, ⟨(-1566416681738368091), (-1566416009976181779)⟩, true⟩

def state01 : KState := ⟨⟨362555899624156419, 362555899850439319⟩, ⟨(-321679258550836092), (-321678582031844920)⟩, true⟩

def words00 : List Nat := [371282876261780309, 371282901130224886, 371282929637109471, 371282958131109063, 371283001647698570, 371283001647818092, 371282976874163946, 371282953093796805, 371282956861176991, 371282973397926999]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 4400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 4400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362259356532759563, 362259356760118869⟩, ⟨988297238983500765, 988297920254968671⟩, true⟩

def words01 : List Nat := [371283014898771026, 371283056380852950, 371283097345566739, 371283097345686418, 371283070268069445, 371283058311681321, 371283055077608162, 371283055077727942, 371283004173484635, 371282953574656193]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 4410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 4400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362469274855806481, 362469275084239668⟩, ⟨60561673257857108, 60562359281352408⟩, true⟩

def words02 : List Nat := [371282903393016296, 371282903393149029, 371282922075144043, 371282956861228514, 371282980053389888, 371282980053509903, 371282935575169108, 371282926366132007, 371282946045578563, 371282946045702728]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 4420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 4400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362370875987625531, 362370876217156793⟩, ⟨496799216593344318, 496799907486932316⟩, true⟩

def words03 : List Nat := [371282942960495040, 371282929780673902, 371282916839630647, 371282916839762916, 371282892138709851, 371282882529450093, 371282872924484026, 371282853732367061, 371282793294612004, 371282768088212409]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 4430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 4400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362325648895040306, 362325649125645925⟩, ⟨698122053102984971, 698122748772324203⟩, true⟩

def words04 : List Nat := [371282768205785243, 371282768205905706, 371282726352301377, 371282684067764905, 371282641802210291, 371282600903908284, 371282545652635818, 371282540793635601, 371282535936778097, 371282530642223976]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 4440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 4400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362608778968504511, 362608779200201797⟩, ⟨(-562534046277041608), (-562533345744202234)⟩, true⟩

def words05 : List Nat := [371282510448023367, 371282525493477835, 371282579900306851, 371282585443124780, 371282585443220003, 371282575782133132, 371282606634883906, 371282622360839054, 371282650647210071, 371282678920949567]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 4450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 4400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362646039241218929, 362646039474009401⟩, ⟨(-729397321932216945), (-729396616518180561)⟩, true⟩

def words06 : List Nat := [371282706739046247, 371282706739167425, 371282710032114583, 371282736701207558, 371282773169547559, 371282787124817844, 371282800667508941, 371282814204178640, 371282863497021706, 371282899993687733]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 4460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 4400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362282587036149847, 362282587270037115⟩, ⟨897919248580758277, 897919958903007719⟩, true⟩

def words07 : List Nat := [371282966242016139, 371283032460773297, 371283087853392456, 371283087853513954, 371283080328566990, 371283083626965337, 371283105145736573, 371283105145858145, 371283060580659019, 371283015832292251]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 4470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 4400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362430711133848363, 362430711368825228⟩, ⟨234648773061034704, 234649488270238064⟩, true⟩

def words08 : List Nat := [371282975965738900, 371282975965873987, 371282988945241784, 371283020199376384, 371283042660911263, 371283042661033062, 371282999263303260, 371282975838385676, 371282971833792832, 371282971833918823]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 4480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 4400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362518762613071533, 362518762849160080⟩, ⟨(-160603003636217096), (-160602283429880824)⟩, true⟩

def words09 : List Nat := [371282960197300971, 371282948666111290, 371282974935150634, 371282995473067439, 371283024279940841, 371283053074050280, 371283081711429495, 371283081711552213, 371283073452691607, 371283081382057241]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 4490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 4400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 4400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk044
