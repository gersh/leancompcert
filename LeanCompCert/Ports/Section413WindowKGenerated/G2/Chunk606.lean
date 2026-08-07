import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk606

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360569578272667014, 360569601671182998⟩, ⟨772421383902646679, 773379301206915753⟩, true⟩

def state01 : KState := ⟨⟨360586492073564712, 360586515480075245⟩, ⟨(-252706798384207840), (-251748396573283432)⟩, true⟩

def words00 : List Nat := [360582363557562105, 360582363558410606, 360582363416695461, 360582363138278129, 360582362859734900, 360582362342183837, 360582362068150451, 360582362066425819, 360582362064608587, 360582361970042854]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 60600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 60600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360601548867491378, 360601572282013126⟩, ⟨(-1165403454502096863), (-1164444567090235887)⟩, true⟩

def words01 : List Nat := [360582362311371815, 360582362652938576, 360582362985492348, 360582363046910934, 360582363047701335, 360582362877583388, 360582362808424876, 360582363046244605, 360582363363813395, 360582363681576145]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 60610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 60600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360585983602485504, 360586007025084393⟩, ⟨(-221854748688152630), (-220895371600258194)⟩, true⟩

def words02 : List Nat := [360582363786187721, 360582363799690783, 360582364085047093, 360582364370651776, 360582364552113209, 360582364552961974, 360582364463320546, 360582364166463288, 360582363869453403, 360582363750660415]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 60620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 60600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360578483215715556, 360578506646305973⟩, ⟨233059450667216706, 234019312320960784⟩, true⟩

def words03 : List Nat := [360582364083388065, 360582364416277475, 360582364613133525, 360582364894666590, 360582365069194081, 360582365243941529, 360582365690349055, 360582365865834598, 360582365866593746, 360582365803831055]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 60630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 60600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360588962851425810, 360588986290042548⟩, ⟨(-402568237305129041), (-401607888895519167)⟩, true⟩

def words04 : List Nat := [360582365740889892, 360582365733737107, 360582365734428446, 360582365734607682, 360582365734724330, 360582365499278328, 360582364992660844, 360582364758151451, 360582364559749583, 360582364669807177]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 60640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 60600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk606
