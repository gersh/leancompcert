import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk020

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360990549967858940, 360990549986076680⟩, ⟨(-857762759828975768), (-857762735037039664)⟩, true⟩

def state01 : KState := ⟨⟨361315878107114482, 361315878125526723⟩, ⟨(-1510482839444322581), (-1510482814262420447)⟩, true⟩

def words00 : List Nat := [360561912699073120, 360562128754409722, 360562587299562544, 360563045387319544, 360563435257933268, 360563796932157210, 360564019091388606, 360564241029458049, 360564394138308323, 360564767825048145]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 2000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 2000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360719185193068239, 360719185211673754⟩, ⟨(-305691103991698736), (-305691078420307442)⟩, true⟩

def words01 : List Nat := [360565381960753570, 360565995486293252, 360566404746425510, 360566757458950639, 360566952000964015, 360567146350080880, 360567580488568002, 360567778040549280, 360567852994612740, 360567927874503884]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 2010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 2000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨361438504042848656, 361438504061649184⟩, ⟨(-1765520718503070056), (-1765520692536789868)⟩, true⟩

def words02 : List Nat := [360568100524136253, 360568402325416576, 360568604069207990, 360568805613749996, 360568805613769193, 360568799848734008, 360568559671975646, 360568557182981369, 360568789434762088, 360569217654688677]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 2020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 2000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360801133183142317, 360801133202140176⟩, ⟨(-468545769192705333), (-468545742824837597)⟩, true⟩

def words03 : List Nat := [360569525021476510, 360569832085889055, 360570216997966272, 360570723624559370, 360571038857685977, 360571353781308612, 360571463818109648, 360571463818130449, 360571453916418079, 360571566449163774]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 2030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 2000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360516827216669833, 360516827235864236⟩, ⟨110475649780802747, 110475676550617235⟩, true⟩

def words04 : List Nat := [360571726006621716, 360571726006642557, 360571653374342475, 360571448496452534, 360571243818928506, 360570972871199684, 360570882369447251, 360570866976360853, 360570851598297195, 360570717809791367]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 2040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 2000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360871573934521169, 360871573953914052⟩, ⟨(-619254784276314350), (-619254757098623174)⟩, true⟩

def words05 : List Nat := [360570691534541008, 360570653530590071, 360570808738237405, 360570968329720613, 360570968329739947, 360570919641964196, 360570871001523290, 360570818850864716, 360570964848504644, 360571110704472702]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 2050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 2000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360356043470940807, 360356043490534663⟩, ⟨440775082514385215, 440775110107085185⟩, true⟩

def words06 : List Nat := [360571128354752156, 360571128354773200, 360570937045309649, 360570955985612258, 360570955985630234, 360570790965330959, 360570398631481989, 360569848585154035, 360569299070524611, 360568978326335188]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 2060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 2000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨359333941189986472, 359333941209780626⟩, ⟨2564553846701169162, 2564553874709492038⟩, true⟩

def words07 : List Nat := [360568875508952252, 360568851895921899, 360568828305670474, 360568687871312778, 360568516323321998, 360568270147473625, 360568024208668694, 360567870902639818, 360567492857045505, 360566899803390959]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 2070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 2000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨361483266322014068, 361483266342009386⟩, ⟨(-1917915440950515216), (-1917915412522748386)⟩, true⟩

def words08 : List Nat := [360566307319701561, 360565940655051782, 360565698034773707, 360565680686169390, 360565663354204802, 360565449040410596, 360565301790598305, 360565340484638659, 360565603465182001, 360566042328368665]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 2080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 2000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360682307186196367, 360682307206396423⟩, ⟨(-241725346747096824), (-241725317890398796)⟩, true⟩

def words09 : List Nat := [360566300239005684, 360566557903194320, 360566676204128131, 360566915323243909, 360567087951574110, 360567260415264650, 360567312941159888, 360567312941181403, 360567199912138098, 360567254699071150]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 2090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 2000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 2000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk020
