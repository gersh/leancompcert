import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk560

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360597864893832214, 360597884749242388⟩, ⟨(-900431744590832228), (-899680505005488022)⟩, true⟩

def state01 : KState := ⟨⟨360583341934813346, 360583361797642055⟩, ⟨(-87254294303453220), (-86502639242940778)⟩, true⟩

def words00 : List Nat := [360581819359633753, 360581819360413385, 360581819135425041, 360581819182638485, 360581819183291944, 360581819060374414, 360581818751357537, 360581818189291033, 360581817627095351, 360581817411017233]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 56000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 56000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360556033148495639, 360556053018667659⟩, ⟨1442557378023844594, 1443309444420060864⟩, true⟩

def words01 : List Nat := [360581817675682767, 360581817940495121, 360581818045657863, 360581818159913839, 360581818160568217, 360581818089932579, 360581818019066378, 360581817928305398, 360581817659221740, 360581817200110360]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 56010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 56000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360569814791536481, 360569834669081363⟩, ⟨670342014971414454, 671094494430368890⟩, true⟩

def words02 : List Nat := [360581816740849925, 360581816198430261, 360581815815658733, 360581815473546498, 360581815131393718, 360581814521167297, 360581813668421728, 360581813072338155, 360581812476030570, 360581812082867378]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 56020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 56000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360565007256832362, 360565027141800163⟩, ⟨939729156274550268, 940482051676814316⟩, true⟩

def words03 : List Nat := [360581811869799747, 360581811461170934, 360581811052405250, 360581810969790482, 360581810970454739, 360581810830858692, 360581810691182529, 360581810392150697, 360581809775355765, 360581809476769414]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 56030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 56000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360574061133577505, 360574081025903998⟩, ⟨432337498494217180, 433090806314469266⟩, true⟩

def words04 : List Nat := [360581809196396766, 360581809224463346, 360581809225168227, 360581809054534033, 360581808883783110, 360581808505355092, 360581808286311997, 360581808253386557, 360581808220390571, 360581807891315497]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 56040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 56000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360595940506709700, 360595960406402756⟩, ⟨(-794155429461965806), (-793401708709888948)⟩, true⟩

def words05 : List Nat := [360581807765918851, 360581807778612734, 360581808108839934, 360581808121775824, 360581808122495963, 360581807823978469, 360581807525299942, 360581807428479667, 360581807681572185, 360581807934832326]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 56050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 56000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360561968393341782, 360561988300486516⟩, ⟨1110357580379699805, 1111111718909252571⟩, true⟩

def words06 : List Nat := [360581808028240439, 360581808029021030, 360581807805022033, 360581807573154542, 360581807341088548, 360581807028721918, 360581806667862319, 360581806067385951, 360581805466785909, 360581804810543753]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 56060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 56000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360541677655562388, 360541697570051896⟩, ⟨2248239827041713198, 2248994377430197226⟩, true⟩

def words07 : List Nat := [360581804457757105, 360581804319972151, 360581804182106714, 360581803885164190, 360581803508286199, 360581803048844847, 360581802589202024, 360581802121718125, 360581801607786339, 360581800893472549]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 56070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 56000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360580868458323751, 360580888380184508⟩, ⟨50262744506351870, 51017708310971108⟩, true⟩

def words08 : List Nat := [360581800179007492, 360581799782206316, 360581799587679033, 360581799498004356, 360581799408258597, 360581799048603473, 360581798523471163, 360581798315941944, 360581798108185299, 360581797948883224]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 56080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 56000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360590661321626710, 360590681250936512⟩, ⟨(-499128513909934904), (-498373132252242670)⟩, true⟩

def words09 : List Nat := [360581797933375173, 360581797671875166, 360581797465257589, 360581797680445622, 360581797719864559, 360581797759406375, 360581797760109772, 360581797593388520, 360581797593490068, 360581797752741253]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 56090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 56000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 56000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk560
