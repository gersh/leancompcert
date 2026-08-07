import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk111

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362452337947410050, 362452339513356539⟩, ⟨375397243856026878, 375409009978658788⟩, true⟩

def state01 : KState := ⟨⟨362453348507974574, 362453350076841916⟩, ⟨364419137765885905, 364430936325215035⟩, true⟩

def words00 : List Nat := [371286159159805776, 371286159160140059, 371286156821569384, 371286154481709124, 371286152189853373, 371286152190216770, 371286150126540928, 371286152017140299, 371286152140976797, 371286152141317633]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 11100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 11100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362631421076676494, 362631422648505929⟩, ⟨(-1614970077115626194), (-1614958245632297494)⟩, true⟩

def words01 : List Nat := [371286152168745956, 371286155148024144, 371286166202257895, 371286166493315637, 371286166493573405, 371286166483744534, 371286174533936720, 371286179528419086, 371286192590073710, 371286205649528113]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 11110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 11100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362500811133295589, 362500812708086310⟩, ⟨(-162327296022640229), (-162315431594781863)⟩, true⟩

def words02 : List Nat := [371286217028529381, 371286219397642544, 371286224615500587, 371286229832585338, 371286236977090098, 371286236977417944, 371286233379958528, 371286229785358488, 371286229110977425, 371286230421535706]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 11120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 11100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362400207565929434, 362400209143672237⟩, ⟨958498138284275649, 958510035583920459⟩, true⟩

def words03 : List Nat := [371286239782976556, 371286249142867978, 371286258476175785, 371286259730455721, 371286261491213029, 371286263251819393, 371286266515852866, 371286266516181250, 371286259061215604, 371286251337171692]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 11130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 11100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362433059908389568, 362433061489071779⟩, ⟨592441808351665596, 592453738411688190⟩, true⟩

def words04 : List Nat := [371286243614373804, 371286241124640669, 371286234641871409, 371286232190316447, 371286229739091019, 371286226067654109, 371286211694193573, 371286203903992152, 371286196353162963, 371286196353503321]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 11140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 11100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362471394420943202, 362471396004632868⟩, ⟨164699922986017691, 164711886593908455⟩, true⟩

def words05 : List Nat := [371286191588724999, 371286184877994831, 371286178168330708, 371286177091614258, 371286173977852033, 371286171250276483, 371286168523082808, 371286165793064398, 371286156456464171, 371286155134255979]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 11150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 11100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362366765896190386, 362366767482808759⟩, ⟨1333113240802509428, 1333125237110267444⟩, true⟩

def words06 : List Nat := [371286160501045283, 371286160501374184, 371286156516385499, 371286152082816007, 371286147649924485, 371286141580765731, 371286131522835248, 371286126684868990, 371286121847657376, 371286116205916214]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 11160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 11100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362515901801920186, 362515903391517594⟩, ⟨(-333256402357285268), (-333244372758817742)⟩, true⟩

def words07 : List Nat := [371286105522340906, 371286102837346177, 371286105463295341, 371286105463624753, 371286101844010088, 371286096618663807, 371286094161977577, 371286094162344086, 371286096202172899, 371286098868419587]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 11170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 11100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362479912032339241, 362479913624908085⟩, ⟨68988233924213822, 69000296758875962⟩, true⟩

def words08 : List Nat := [371286101531175055, 371286101531504508, 371286093559104061, 371286092130320881, 371286091625861275, 371286091626197471, 371286088101008570, 371286083248744653, 371286079870891913, 371286079871267234]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 11180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 11100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362460110890106986, 362460112485656531⟩, ⟨290814727256005084, 290826823459739920⟩, true⟩

def words09 : List Nat := [371286083887517412, 371286088454087288, 371286091229895738, 371286091230225980, 371286085615912846, 371286082363894064, 371286083815914227, 371286083816246452, 371286081484601562, 371286079166322580]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 11190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 11100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 11100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk111
