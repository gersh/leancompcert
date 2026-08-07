import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk913

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362482478856480607, 362482605130163664⟩, ⟨220561150497671118, 228345131503408744⟩, true⟩

def state01 : KState := ⟨⟨362487338703732384, 362487465005954542⟩, ⟨(-223157717260568852), (-215371130486439984)⟩, true⟩

def words00 : List Nat := [371285106169587014, 371285106173102129, 371285106220710277, 371285106306855715, 371285106372408587, 371285106375598573, 371285106296475786, 371285106266872796, 371285106321993757, 371285106351132161]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 91300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 91300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362485817348403752, 362485943679704443⟩, ⟨(-84223123995525560), (-76433881914770410)⟩, true⟩

def words01 : List Nat := [371285106357263063, 371285106364513698, 371285106478145097, 371285106548740459, 371285106622846964, 371285106698107851, 371285106765989316, 371285106769179417, 371285106686214097, 371285106699361316]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 91310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 91300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362484051743019968, 362484178102779167⟩, ⟨77052081116710107, 84843922174554271⟩, true⟩

def words02 : List Nat := [371285106774676370, 371285106784302192, 371285106795612474, 371285106807958104, 371285106842894639, 371285106846413486, 371285106919318522, 371285107012595045, 371285107081433525, 371285107084736625]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 91320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 91300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362496221274563233, 362496347663122907⟩, ⟨(-1034468876967270156), (-1026674405416569568)⟩, true⟩

def words03 : List Nat := [371285107186359156, 371285107299808906, 371285107433057609, 371285107436248234, 371285107410041785, 371285107365688072, 371285107377708772, 371285107394149469, 371285107519372971, 371285107645984749]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 91330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 91300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362483434041194952, 362483560458615921⟩, ⟨133528286457775013, 141325394338910389⟩, true⟩

def words04 : List Nat := [371285107761822862, 371285107765013999, 371285107753546918, 371285107775597942, 371285107832789090, 371285107835980135, 371285107733627270, 371285107632204287, 371285107530888206, 371285107534634957]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 91340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 91300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362467557719437584, 362467684165600324⟩, ⟨1583945670445081396, 1591745404035440284⟩, true⟩

def words05 : List Nat := [371285107583002202, 371285107649628192, 371285107702893434, 371285107706084673, 371285107599561930, 371285107495128234, 371285107389110355, 371285107323705648, 371285107135118477, 371285106948043795]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 91350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 91300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362485214083189632, 362485340557916215⟩, ⟨(-29208852428432447), (-21406509100308355)⟩, true⟩

def words06 : List Nat := [371285106759505536, 371285106678532977, 371285106536437917, 371285106506154566, 371285106474830401, 371285106425070204, 371285106266921947, 371285106230198087, 371285106270830481, 371285106276698977]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 91360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 91300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362483802351927304, 362483928855737493⟩, ⟨99799686335629316, 107604687180485266⟩, true⟩

def words07 : List Nat := [371285106279131775, 371285106255828872, 371285106324202278, 371285106364060064, 371285106407923332, 371285106453040847, 371285106476196891, 371285106479445642, 371285106416545087, 371285106407577945]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 91370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 91300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362481579014846539, 362481705547071080⟩, ⟨302980692234125254, 310788289729328524⟩, true⟩

def words08 : List Nat := [371285106503636758, 371285106506829240, 371285106456428451, 371285106405001629, 371285106352364188, 371285106306298886, 371285106208890524, 371285106222393735, 371285106225322283, 371285106228652537]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 91380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 91300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362492125032936968, 362492251594089350⟩, ⟨(-660842890557392888), (-653032649207284246)⟩, true⟩

def words09 : List Nat := [371285106254261251, 371285106318860634, 371285106501317170, 371285106525270098, 371285106531839380, 371285106539348846, 371285106665217830, 371285106732735174, 371285106813124673, 371285106894915301]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 91390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 91300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 91300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk913
