import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk896

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360583629752239388, 360583682504429377⟩, ⟨(-150113643735580007), (-146921844977708617)⟩, true⟩

def state01 : KState := ⟨⟨360576858424769855, 360576911189268016⟩, ⟨456577090477213287, 459769992106887305⟩, true⟩

def words00 : List Nat := [360582042771147328, 360582042728216958, 360582042597252898, 360582042591105024, 360582042584597823, 360582042546888605, 360582042490001501, 360582042318203377, 360582042146164674, 360582041978154378]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 89600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 89600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360567961944792330, 360568014721449444⟩, ⟨1253923167694077599, 1257117158950332291⟩, true⟩

def words01 : List Nat := [360582041989083970, 360582042057516681, 360582042061918300, 360582042105993578, 360582042118429583, 360582042131208433, 360582042162590268, 360582042163883057, 360582042070995961, 360582041915813987]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 89610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 89600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360577248329991511, 360577301118877593⟩, ⟨421575923254590999, 424771010528688881⟩, true⟩

def words02 : List Nat := [360582041760361637, 360582041559245156, 360582041437643035, 360582041325673622, 360582041213604139, 360582040993904001, 360582040700645798, 360582040532158732, 360582040363261174, 360582040279990264]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 89620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 89600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360558661459732001, 360558714260933116⟩, ⟨2087660939356725969, 2090857130488187945⟩, true⟩

def words03 : List Nat := [360582040228280483, 360582040095869880, 360582039963214328, 360582040008331281, 360582040009437288, 360582039960903577, 360582039912229899, 360582039801251599, 360582039565732056, 360582039307011744]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 89630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 89600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360573274655505862, 360573327468903716⟩, ⟨777647207000279062, 780844491507858616⟩, true⟩

def words04 : List Nat := [360582039047854648, 360582038830900248, 360582038659710212, 360582038426235296, 360582038192554330, 360582037927867099, 360582037743627980, 360582037658825485, 360582037573908705, 360582037390727563]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 89640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 89600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360606013704031578, 360606066529623744⟩, ⟨(-2157619805349085512), (-2154421427560993564)⟩, true⟩

def words05 : List Nat := [360582037294619721, 360582037272061419, 360582037349405501, 360582037394049821, 360582037395243085, 360582037330186416, 360582037322747785, 360582037467941833, 360582037736989227, 360582038006324194]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 89650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 89600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360589647995188915, 360589700833115003⟩, ⟨(-690329510192597564), (-687130026488459720)⟩, true⟩

def words06 : List Nat := [360582038169564605, 360582038238465393, 360582038304222465, 360582038370339969, 360582038384452712, 360582038385746265, 360582038305214031, 360582038148021300, 360582037990582935, 360582038043288990]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 89660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 89600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360562940584225123, 360562993434331583⟩, ⟨1704750389603824122, 1707950965582325048⟩, true⟩

def words07 : List Nat := [360582038254014072, 360582038464991271, 360582038602276450, 360582038703955832, 360582038728330295, 360582038753057455, 360582038754122788, 360582038736064571, 360582038593679927, 360582038382654312]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 89670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 89600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360574712864959777, 360574765727267989⟩, ⟨648956332839583168, 652158003133696792⟩, true⟩

def words08 : List Nat := [360582038171336680, 360582038084611512, 360582038059853106, 360582038018518436, 360582037977072821, 360582037828447088, 360582037555416622, 360582037319933843, 360582037084075313, 360582036972703754]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 89680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 89600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360582924555178673, 360582977429835727⟩, ⟨(-87616002983126402), (-84413225064505992)⟩, true⟩

def words09 : List Nat := [360582036892806527, 360582036717934785, 360582036542815404, 360582036493397228, 360582036494479874, 360582036488206727, 360582036481793649, 360582036399376589, 360582036366753696, 360582036378731899]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 89690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 89600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 89600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk896
