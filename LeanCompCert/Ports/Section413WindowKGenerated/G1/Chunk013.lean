import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk013

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362068597662450824, 362068597679648890⟩, ⟨512797036731409079, 512797051941150449⟩, true⟩

def state01 : KState := ⟨⟨362447548582091684, 362447548599570551⟩, ⟨24014649969789913, 24014665546039751⟩, true⟩

def words00 : List Nat := [371263033528523919, 371263120501623168, 371263788582005028, 371264455638521560, 371265017851617887, 371265017851649240, 371265177445667363, 371265545834254271, 371265880405298344, 371265880405330887]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 1300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 1300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362418997513617659, 362418997531385281⟩, ⟨61768150260459640, 61768166216444860⟩, true⟩

def words01 : List Nat := [371265866422283925, 371265796615433089, 371265981395120912, 371265981395155921, 371266125314991078, 371266277670894808, 371266430852937763, 371266430852969499, 371265827073587278, 371265791596700770]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 1310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 1300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362471718163802414, 362471718181854665⟩, ⟨(-8370292036739279), (-8370275703558225)⟩, true⟩

def words02 : List Nat := [371266287342380829, 371266287342412623, 371266064393947643, 371265729983049054, 371265396076910040, 371265207546478065, 371265033623982846, 371265227318163767, 371265424741442343, 371265429469830955]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 1320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 1300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362959813133761158, 362959813152104547⟩, ⟨(-659292464526249500), (-659292447804348456)⟩, true⟩

def words03 : List Nat := [371265725355885285, 371266020798015626, 371266709676750708, 371266903286327320, 371266994491482856, 371267085560215987, 371267397355104736, 371267436417315651, 371267803862662389, 371268170760005854]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 1330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 1300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362276997200834472, 362276997219472183⟩, ⟨257971709748503734, 257971726866283934⟩, true⟩

def words04 : List Nat := [371268511029078839, 371268511029111536, 371268606148255549, 371268811834108959, 371269172846023379, 371269172846055976, 371268808590572678, 371268448458068905, 371268088859477710, 371268087387521283]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 1340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 1300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨361448790224276022, 361448790243209787⟩, ⟨1381021842274285602, 1381021859793261032⟩, true⟩

def words05 : List Nat := [371268029461937088, 371268112856409673, 371268112856434434, 371268047153839626, 371267266360875094, 371266646224487030, 371266027002064338, 371265724514432548, 371264994702181577, 371264247493057774]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 1350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 1300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362048281640888560, 362048281660118828⟩, ⟨564913495910846027, 564913513834606403⟩, true⟩

def words06 : List Nat := [371263501381948935, 371263284589622760, 371262805435778533, 371262668643640233, 371262532051920549, 371262313201867586, 371261393150256025, 371260997556541805, 371260627290620711, 371260627290655038]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 1360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 1300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362029853889217666, 362029853908751954⟩, ⟨592184394767277223, 592184413109102379⟩, true⟩

def words07 : List Nat := [371260326528002803, 371260029789352041, 371259956782814372, 371259956782850959, 371259919458072373, 371259906432065134, 371259893424966259, 371259816145175971, 371259284230037619, 371258973048686087]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 1370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 1300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨361873285348509572, 361873285368343392⟩, ⟨810438722084324217, 810438740841081841⟩, true⟩

def words08 : List Nat := [371258866158577124, 371258866158610718, 371258383614713026, 371257905438023116, 371257427951828286, 371257107048439086, 371256646545237820, 371256540497594498, 371256434602636815, 371256334822185897]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 1380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 1300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362571592714672918, 362571592734813560⟩, ⟨(-164344572206758716), (-164344553021962774)⟩, true⟩

def words09 : List Nat := [371255915663723249, 371255814877127822, 371255836595843464, 371255836595877405, 371255490154985905, 371255091151395296, 371254692719020937, 371254534608952121, 371254203768330487, 371254287557781467]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 1390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 1300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 1300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk013
