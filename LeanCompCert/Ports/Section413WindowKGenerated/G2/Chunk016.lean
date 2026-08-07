import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk016

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360145376028496016, 360145376039847080⟩, ⟨566613660030356979, 566613672408653271⟩, true⟩

def state01 : KState := ⟨⟨362236537711533032, 362236537723036146⟩, ⟨(-2792592008226371106), (-2792591995604023164)⟩, true⟩

def words00 : List Nat := [360499449131682579, 360499821393844256, 360500155927735330, 360500490044764567, 360500494667644560, 360500494667660782, 360500873359407225, 360501251823384621, 360502008533203023, 360503085211798392]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 1600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 1600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨361847660605453335, 361847660617110740⟩, ⟨(-2163811121420292074), (-2163811108548764076)⟩, true⟩

def words01 : List Nat := [360503961196089018, 360504836094226052, 360506087225657022, 360507538396590062, 360508712216546457, 360509884584656414, 360510699530117181, 360511149740890762, 360511974747617657, 360512798736451417]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 1610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 1600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362021305693610397, 362021305705420988⟩, ⟨(-2447242803410951025), (-2447242790290472955)⟩, true⟩

def words02 : List Nat := [360513996604925177, 360514830123801683, 360515461857814195, 360516092814310012, 360516519043881189, 360517141993879353, 360518136432280929, 360519129649766847, 360519929760440670, 360520850285255156]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 1620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 1600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362629785640455107, 362629785652420522⟩, ⟨(-3444890620053131533), (-3444890606679517783)⟩, true⟩

def words03 : List Nat := [360521736173870149, 360522620977506649, 360523603151405348, 360524514775096657, 360525118226050199, 360525720939740675, 360526690549128192, 360527960999138421, 360529242599550169, 360530522637990591]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 1630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 1600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨361264776864042405, 361264776876164802⟩, ⟨(-1204101183912648526), (-1204101170280806094)⟩, true⟩

def words04 : List Nat := [360531604199461703, 360532331717000742, 360533194794565172, 360534056822799877, 360534648710728678, 360534887967936806, 360534912891750730, 360534937785337356, 360535018591127271, 360535460601009862]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 1640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 1600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨359750255836926780, 359750255849205989⟩, ⟨1303875757740519685, 1303875771631911453⟩, true⟩

def words05 : List Nat := [360535966978651083, 360536472743618520, 360536730482031181, 360536730482047817, 360536638506472386, 360536436163002476, 360536389743708612, 360536389743725284, 360536196639804725, 360535723181514370]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 1650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 1600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨361727873256258458, 361727873268695545⟩, ⟨(-1991341236432560370), (-1991341222278287396)⟩, true⟩

def words06 : List Nat := [360535250293308708, 360534795646661610, 360534615116963667, 360534702549426037, 360534702549441564, 360534451790714856, 360534599168017215, 360534849624289881, 360535453375098432, 360536166971700760]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 1660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 1600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360668814499564535, 360668814512161987⟩, ⟨(-216645231483598797), (-216645217060718709)⟩, true⟩

def words07 : List Nat := [360536689519867627, 360537211443352472, 360537699814355699, 360538384382057803, 360538939292187440, 360539493540530707, 360539807993669869, 360539807993686725, 360539859025796927, 360539935739371554]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 1670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 1600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360248500406273179, 360248500419029825⟩, ⟨490431576144494632, 490431590835635728⟩, true⟩

def words08 : List Nat := [360540229392608797, 360540326020516137, 360540326020531444, 360540105623075009, 360539885487215257, 360539558746313254, 360539410779224346, 360539233901774909, 360539057233770039, 360538696626624876]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 1680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 1600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362260230348214330, 362260230361131663⟩, ⟨(-2921684248985683726), (-2921684234022175650)⟩, true⟩

def words09 : List Nat := [360538525014452080, 360538452122459146, 360538648472645236, 360539093616025158, 360539252022172045, 360539410241630663, 360539909204459331, 360540581017944017, 360541592576395063, 360542602945480767]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 1690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 1600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 1600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk016
