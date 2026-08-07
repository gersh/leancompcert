import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk889

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362483703390470344, 362483822867080403⟩, ⟨111096033649061559, 118267558755346945⟩, true⟩

def state01 : KState := ⟨⟨362489393164199524, 362489512668519006⟩, ⟨(-394713235732833501), (-387539247115255357)⟩, true⟩

def words00 : List Nat := [371285153276348395, 371285153314518064, 371285153477688504, 371285153642144707, 371285153785637306, 371285153788735973, 371285153765693364, 371285153771634659, 371285153883982473, 371285153936223618]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 88900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 88900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362491320569325644, 362491440101952219⟩, ⟨(-566098903085829955), (-558922397551699907)⟩, true⟩

def words01 : List Nat := [371285153975107851, 371285154015053525, 371285154095157813, 371285154143956588, 371285154230096284, 371285154317393770, 371285154400781494, 371285154403885422, 371285154421034366, 371285154495655038]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 88910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 88900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362478735962689510, 362478855522950777⟩, ⟨552993928996506473, 560172891951290025⟩, true⟩

def words02 : List Nat := [371285154621050477, 371285154624150109, 371285154594470707, 371285154565784104, 371285154541858349, 371285154545274480, 371285154513021863, 371285154539328706, 371285154551473868, 371285154554683053]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 88920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 88900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362491514872153173, 362491634460373328⟩, ⟨(-583489582724416289), (-576308133242182763)⟩, true⟩

def words03 : List Nat := [371285154533143098, 371285154584007092, 371285154717395073, 371285154720495834, 371285154703577177, 371285154640850190, 371285154636995713, 371285154641306839, 371285154716271213, 371285154792579598]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 88930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 88900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362486471308552902, 362486590924786699⟩, ⟨(-134898251298100392), (-127714310142104004)⟩, true⟩

def words04 : List Nat := [371285154857521964, 371285154860676267, 371285154872288361, 371285154928090401, 371285155020911515, 371285155037856208, 371285155054620192, 371285155072383256, 371285155122367789, 371285155142050788]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 88940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 88900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362481303862268797, 362481423506452737⟩, ⟨324824540289124048, 332010967752186370⟩, true⟩

def words05 : List Nat := [371285155286536483, 371285155432309193, 371285155575590490, 371285155578691441, 371285155594463410, 371285155624337175, 371285155717247613, 371285155720355051, 371285155682553022, 371285155644129808]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 88950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 88900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362486527714299865, 362486647386258634⟩, ⟨(-139928425041667995), (-132739526589087575)⟩, true⟩

def words06 : List Nat := [371285155642352252, 371285155645769622, 371285155637788825, 371285155656024432, 371285155658448834, 371285155659526605, 371285155491289585, 371285155428844607, 371285155424725847, 371285155444765462]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 88960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 88900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362485870718453366, 362485990418629070⟩, ⟨(-81443919216349882), (-74252510158538922)⟩, true⟩

def words07 : List Nat := [371285155458209700, 371285155472692450, 371285155605855023, 371285155676920197, 371285155784756725, 371285155893818530, 371285155970138526, 371285155973248645, 371285155929429117, 371285155942615556]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 88970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 88900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362477629369387201, 362477749097167753⟩, ⟨651919126619305380, 659112992100991906⟩, true⟩

def words08 : List Nat := [371285156061948910, 371285156065050738, 371285156016366576, 371285155969456063, 371285155921281631, 371285155885772663, 371285155785909432, 371285155755450329, 371285155723971953, 371285155693325760]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 88980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 88900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362493219091541699, 362493338847441249⟩, ⟨(-735516331741944086), (-728319963816205778)⟩, true⟩

def words09 : List Nat := [371285155612237444, 371285155585272177, 371285155651971702, 371285155655073901, 371285155584629961, 371285155479532197, 371285155390862847, 371285155394358340, 371285155473542195, 371285155569008241]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 88990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 88900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 88900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk889
