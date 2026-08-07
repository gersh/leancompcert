import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk411

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362484162303413898, 362484186326234735⟩, ⟨36524328354395188, 37191486621733248⟩, true⟩

def state01 : KState := ⟨⟨362460289158989600, 362460313193837920⟩, ⟨1017874821519949316, 1018542474179305762⟩, true⟩

def words00 : List Nat := [371285091609914371, 371285091611264482, 371285091226555152, 371285090842528495, 371285090457961149, 371285090252285714, 371285089880971333, 371285089663825041, 371285089446245732, 371285089220940312]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 41100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 41100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362495595221870578, 362495619268962203⟩, ⟨(-433768565933728547), (-433100409890797921)⟩, true⟩

def words01 : List Nat := [371285088619211360, 371285088257336254, 371285088122087959, 371285088123438892, 371285087647931761, 371285087082976435, 371285086541919708, 371285086543443786, 371285086669908798, 371285086927582111]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 41110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 41100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362451988159891257, 362452012219165601⟩, ⟨1359520301745512722, 1360188958804669204⟩, true⟩

def words02 : List Nat := [371285087181124076, 371285087182476433, 371285086804862132, 371285086610125948, 371285086414762730, 371285086241449076, 371285085280521156, 371285084319588819, 371285083358148077, 371285082701995766]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 41120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 41100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362439687358526975, 362439711429980096⟩, ⟨1865644551964768957, 1866313709998781261⟩, true⟩

def words03 : List Nat := [371285081898884740, 371285081686738174, 371285081474126168, 371285081261395150, 371285080336715107, 371285079548248394, 371285078759103441, 371285078463459893, 371285077473089803, 371285076371885755]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 41130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 41100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362479417283465923, 362479441367005229⟩, ⟨231031202682815060, 231700858004566386⟩, true⟩

def words04 : List Nat := [371285075270133200, 371285074759115062, 371285073952521212, 371285073736623341, 371285073520307855, 371285073238568842, 371285072465021684, 371285072116175826, 371285072006138956, 371285072007539970]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 41140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 41100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362475859720677932, 362475883816568845⟩, ⟨377414821829571863, 378084985481476019⟩, true⟩

def words05 : List Nat := [371285071871730280, 371285071569045568, 371285071265823055, 371285071208825174, 371285070922869018, 371285070815170425, 371285070707045565, 371285070522381931, 371285069776258606, 371285069554797258]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 41150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 41100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362471657882733370, 362471681990657289⟩, ⟨550466718047681421, 551137377041195997⟩, true⟩

def words06 : List Nat := [371285069698924419, 371285069700285814, 371285069538741139, 371285069377394595, 371285069230547823, 371285069232051485, 371285068954284320, 371285068922796828, 371285068890836070, 371285068859179058]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 41160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 41100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362512651879920856, 362512676000051213⟩, ⟨(-1137505491148856383), (-1136834329554297391)⟩, true⟩

def words07 : List Nat := [371285068595986213, 371285068658624683, 371285068920244257, 371285068921624229, 371285068823800526, 371285068612491728, 371285068776858065, 371285068859774059, 371285069531093911, 371285070202971145]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 41170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 41100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362494984272409324, 362495008404772391⟩, ⟨(-409961383343355080), (-409289717946050006)⟩, true⟩

def words08 : List Nat := [371285070729476033, 371285070730829555, 371285070964574949, 371285071377092337, 371285071966682955, 371285071968036292, 371285071772750142, 371285071577933152, 371285071774971325, 371285072017747409]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 41180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 41100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362462426364932317, 362462450509485728⟩, ⟨931356073002410643, 932028240582424797⟩, true⟩

def words09 : List Nat := [371285072635758779, 371285073254302679, 371285073849192447, 371285073850546592, 371285073764825542, 371285073602509487, 371285073661642301, 371285073662996142, 371285073101711890, 371285072554160059]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 41190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 41100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 41100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk411
