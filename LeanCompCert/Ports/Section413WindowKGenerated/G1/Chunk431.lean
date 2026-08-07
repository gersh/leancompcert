import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk431

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362528121949947216, 362528148469579168⟩, ⟨(-1841129374338086621), (-1840357078569776589)⟩, true⟩

def state01 : KState := ⟨⟨362517031075613063, 362517057608082141⟩, ⟨(-1363085639276660003), (-1362312790161878539)⟩, true⟩

def words00 : List Nat := [371285450750369456, 371285451163753204, 371285452115795443, 371285453068549162, 371285454108227861, 371285454702157072, 371285455293642044, 371285455885573432, 371285456753043899, 371285457487691478]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 43100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 43100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362497523681864944, 362497550227166624⟩, ⟨(-521951607635594121), (-521178205243174489)⟩, true⟩

def words01 : List Nat := [371285458612164395, 371285459737177301, 371285460753774630, 371285461053339175, 371285461512456652, 371285461972238902, 371285462970039584, 371285463251055226, 371285463532439795, 371285463814392265]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 43110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 43100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362482771740021355, 362482798298039648⟩, ⟨114312593789504978, 115086544588247690⟩, true⟩

def words02 : List Nat := [371285464380940087, 371285464680744205, 371285465375025278, 371285466069838129, 371285466635976060, 371285466637398483, 371285466486460519, 371285466475990274, 371285466660686206, 371285466662161797]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 43120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 43100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362492552372728430, 362492578943689490⟩, ⟨(-307542640133856401), (-306768131047111465)⟩, true⟩

def words03 : List Nat := [371285466601366312, 371285466437764115, 371285466646895972, 371285466890734632, 371285467293922496, 371285467697655868, 371285468099758573, 371285468101181686, 371285467951423797, 371285468118000538]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 43130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 43100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362485447880711194, 362485474464372356⟩, ⟨(-974164189762193), (-199107156398251)⟩, true⟩

def words04 : List Nat := [371285468505528422, 371285468514274621, 371285468549926208, 371285468586068380, 371285468781714768, 371285468790691273, 371285469147655538, 371285469505192873, 371285469848594565, 371285469850176709]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 43140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 43100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362515264835617991, 362515291432149832⟩, ⟨(-1287737802579575375), (-1286962190112507077)⟩, true⟩

def words05 : List Nat := [371285470389139768, 371285470928835753, 371285471743607351, 371285471842785119, 371285471843916534, 371285471803652835, 371285472182791043, 371285472337599103, 371285473029462011, 371285473721945887]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 43150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 43100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362489710147823391, 362489736757217284⟩, ⟨(-184678797016129971), (-183902629357974625)⟩, true⟩

def words06 : List Nat := [371285474411490393, 371285474656440009, 371285475237196163, 371285475818670815, 371285476479795687, 371285476505676360, 371285476528898518, 371285476552623116, 371285476791976434, 371285476892276515]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 43160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 43100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362463919895942118, 362463946518144227⟩, ⟨928901118802222215, 929677839456002925⟩, true⟩

def words07 : List Nat := [371285477373353082, 371285477854972170, 371285478294183666, 371285478295607977, 371285478019425063, 371285477751023851, 371285477748915145, 371285477750339496, 371285477303266150, 371285476806227970]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 43170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 43100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362491163157446134, 362491189792417456⟩, ⟨(-247611731165357795), (-246834459071106489)⟩, true⟩

def words08 : List Nat := [371285476308590089, 371285476206415069, 371285475836291881, 371285475670487791, 371285475504230024, 371285475259748829, 371285474695255794, 371285474521123266, 371285474707354430, 371285474841175969]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 43180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 43100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362479929857588025, 362479956505565357⟩, ⟨237691077356811762, 238468911242779632⟩, true⟩

def words09 : List Nat := [371285474973683347, 371285475106667738, 371285475684577917, 371285476039026853, 371285476508987145, 371285476979457533, 371285477218968144, 371285477220393423, 371285476745229006, 371285476619251533]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 43190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 43100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 43100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk431
