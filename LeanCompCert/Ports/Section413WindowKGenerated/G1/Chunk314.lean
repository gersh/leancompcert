import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk314

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362526179698415102, 362526193412755478⟩, ⟨(-1281922580163932893), (-1281631507553960463)⟩, true⟩

def state01 : KState := ⟨⟨362492390603171799, 362492404326647738⟩, ⟨(-220771837795872018), (-220480478282198974)⟩, true⟩

def words00 : List Nat := [371285379726999017, 371285380190811132, 371285381492183689, 371285382793984135, 371285384107882179, 371285384256545895, 371285384331736831, 371285384407279509, 371285384889691227, 371285385114324597]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 31400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 31400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362477777725402025, 362477791457967646⟩, ⟨238403805104161870, 238695450169937900⟩, true⟩

def words01 : List Nat := [371285386188925238, 371285387263858639, 371285388253236253, 371285388254247311, 371285388044975491, 371285388027871253, 371285388857588335, 371285388858600897, 371285388625757869, 371285388385089541]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 31410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 31400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362484505670693703, 362484519412322803⟩, ⟨26996808637624347, 27288738524308767⟩, true⟩

def words02 : List Nat := [371285388577962407, 371285388579076186, 371285388756163744, 371285389006843654, 371285389087294958, 371285389088308427, 371285388123101056, 371285387687382770, 371285387649836639, 371285387650901369]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 31420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 31400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362492581301793789, 362492595052641997⟩, ⟨(-226850671549616809), (-226558451859573485)⟩, true⟩

def words03 : List Nat := [371285387624034206, 371285387600590601, 371285388067151136, 371285388214791105, 371285388672793079, 371285389131144455, 371285389401254592, 371285389402273018, 371285388993747359, 371285389224205893]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 31430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 31400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362455804857277476, 362455818617137888⟩, ⟨929643347813336992, 929935850894286650⟩, true⟩

def words04 : List Nat := [371285390164824166, 371285390165836044, 371285389910316777, 371285389557194630, 371285389203700183, 371285389057245845, 371285388410633778, 371285388119424414, 371285387827888897, 371285387324638502]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 31440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 31400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362494280902793222, 362494294671802766⟩, ⟨(-280690520384454870), (-280397729517014074)⟩, true⟩

def words05 : List Nat := [371285386385185846, 371285385866719607, 371285385713944617, 371285385714956751, 371285384736756896, 371285383578555057, 371285382420002124, 371285382163294485, 371285381837556931, 371285382121994527]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 31450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 31400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362456821542753110, 362456835320880874⟩, ⟨897861484852431796, 898154562625795396⟩, true⟩

def words06 : List Nat := [371285382409357282, 371285382410369523, 371285381353306945, 371285381190139304, 371285381026472210, 371285380842474333, 371285379314310721, 371285377655707804, 371285375996808590, 371285375345114297]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 31460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 31400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362423276696445292, 362423290483706546⟩, ⟨1953797807721909900, 1954091172973237656⟩, true⟩

def words07 : List Nat := [371285374438939009, 371285374060919571, 371285373682561619, 371285373294887792, 371285371563663310, 371285370132372236, 371285368700659250, 371285368275419682, 371285366506988469, 371285364536215226]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 31470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 31400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362479235667398428, 362479249463735738⟩, ⟨192004108604018913, 192297759614296989⟩, true⟩

def words08 : List Nat := [371285362565108677, 371285361600439379, 371285360310950367, 371285359767949346, 371285359224674267, 371285358515551173, 371285357245981140, 371285356526769440, 371285356092080603, 371285356093129651]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 31480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 31400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362458348119257237, 362458361924832384⟩, ⟨849891287357474067, 850185229312891689⟩, true⟩

def words09 : List Nat := [371285355899977831, 371285355698635331, 371285355496920125, 371285355388355492, 371285354887124267, 371285354696107923, 371285354504752567, 371285354317044185, 371285352787687896, 371285351932112159]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 31490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 31400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 31400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk314
