import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk606A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk606B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk606A

def state06 : KState := ⟨⟨360596620555190037, 360596644001897748⟩, ⟨(-867084833872067185), (-866123994704716203)⟩, true⟩

def words05 : List Nat := [360582364670571680, 360582364608613938, 360582364699137213, 360582365062017867, 360582365240869335, 360582365419843588, 360582365462141117, 360582365462994499, 360582365662728562, 360582365899085320]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 60650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 60600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360594385586480077, 360594409041192322⟩, ⟨(-731429423730680393), (-730468098967845435)⟩, true⟩

def words06 : List Nat := [360582366406859610, 360582366927801834, 360582367300167395, 360582367672613508, 360582367869966108, 360582368203068526, 360582368545718000, 360582368888517759, 360582369018902634, 360582369218229658]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 60660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 60600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360612078040510046, 360612101503241227⟩, ⟨(-1805025299264956518), (-1804063487953970842)⟩, true⟩

def words07 : List Nat := [360582369484444158, 360582369750895998, 360582370008392095, 360582370140513768, 360582370141297901, 360582370038796562, 360582370016366511, 360582370235701554, 360582370726356467, 360582371217188691]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 60670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 60600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360593437180398606, 360593460651232621⟩, ⟨(-674008905172221633), (-673046602142590251)⟩, true⟩

def words08 : List Nat := [360582371566613596, 360582371645456774, 360582371716016428, 360582371786815563, 360582371787526743, 360582371743233505, 360582371581692391, 360582371211227835, 360582370840612643, 360582370924549216]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 60680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 60600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360557343194408632, 360557366673241580⟩, ⟨1516783510006314261, 1517746298531193761⟩, true⟩

def words09 : List Nat := [360582371322076075, 360582371719752705, 360582371980871479, 360582371981721306, 360582371972228828, 360582371859172946, 360582371745878846, 360582371416721179, 360582371141932433, 360582370730878009]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 60690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 60600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 60600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk606B
