import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk017

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨363480907162042295, 363480907192461209⟩, ⟨(-1723485868369978695), (-1723485833198365395)⟩, true⟩

def state01 : KState := ⟨⟨362879787659086563, 362879787689884602⟩, ⟨(-700982976310552013), (-700982940492479887)⟩, true⟩

def words00 : List Nat := [371268215675716561, 371268416153736322, 371268824292612003, 371269231952753715, 371269657617043987, 371269657617085930, 371269629004463512, 371269590820631369, 371269856145688772, 371270095731677425]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 1700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 1700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362012956630019004, 362012956661196896⟩, ⟨787888659001842370, 787888695471420558⟩, true⟩

def words01 : List Nat := [371270537465236568, 371270978683070276, 371271410552160060, 371271410552202162, 371271392745350049, 371271391755720680, 371271567887075340, 371271567887117587, 371271297961598061, 371271031484145397]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 1710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 1700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362076765463260036, 362076765494818613⟩, ⟨682290921418727835, 682290958545025253⟩, true⟩

def words02 : List Nat := [371270835105402074, 371270835105449376, 371271078921231784, 371271368066549007, 371271576786200780, 371271576786243238, 371271342035250646, 371271261780262855, 371271181618087241, 371271153332127877]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 1720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 1700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362465176152324647, 362465176184271360⟩, ⟨9157132134400652, 9157169934195006⟩, true⟩

def words03 : List Nat := [371270925494010096, 371270690372979025, 371270552182558779, 371270552182605759, 371270559662875607, 371270607718801891, 371270660858570131, 371270660858613111, 371270441951863922, 371270438925612852]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 1730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 1700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362546224816410817, 362546224848741178⟩, ⟨(-130897000717594087), (-130896962248253137)⟩, true⟩

def words04 : List Nat := [371270761017288027, 371270801150000085, 371270801150032826, 371270786375518147, 371270845838914976, 371270845838962627, 371271002221011301, 371271243395216309, 371271426584554032, 371271469302054569]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 1740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 1700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨363135313476710869, 363135313509431635⟩, ⟨(-1164990602303053194), (-1164990563148519266)⟩, true⟩

def words05 : List Nat := [371271691532916820, 371271913510257780, 371272459701044628, 371272575850429290, 371272661821024548, 371272747693771618, 371272956617857934, 371273010744629393, 371273387053047995, 371273762934105957]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 1750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 1700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362346679423414911, 362346679456526994⟩, ⟨225370155001554065, 225370194846804951⟩, true⟩

def words06 : List Nat := [371274128927352906, 371274128927396222, 371274208309266406, 371274347335818102, 371274575182694445, 371274575182737834, 371274379746385974, 371274188459940910, 371274007250176368, 371274007250225754]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 1760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 1700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨361881041774262468, 361881041807767976⟩, ⟨1051475411664631520, 1051475452208290468⟩, true⟩

def words07 : List Nat := [371273935354268868, 371273870445409188, 371273805609754999, 371273750210950081, 371273275531346948, 371272883092054730, 371272491094427299, 371272414057794576, 371272090403676822, 371271758353952409]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 1770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 1700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362651411538540617, 362651411572439666⟩, ⟨(-322909622721862169), (-322909581475663333)⟩, true⟩

def words08 : List Nat := [371271426677089618, 371271284895358729, 371271091619999960, 371271151245092450, 371271151245127171, 371271099887920365, 371270767129293492, 371270746108939060, 371271015158161856, 371271115882056828]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 1780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 1700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362574485098685243, 362574485132989556⟩, ⟨(-183719214831869784), (-183719172858217184)⟩, true⟩

def words09 : List Nat := [371271227465264213, 371271338924021973, 371271588369033337, 371271734356204674, 371271966914204708, 371272199213391924, 371272423868352195, 371272423868396709, 371272418925790568, 371272475597810091]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 1790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 1700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 1700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk017
