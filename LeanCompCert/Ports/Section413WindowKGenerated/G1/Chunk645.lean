import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk645

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362496860760250367, 362496922107402526⟩, ⟨(-737390942438856678), (-734718351941622102)⟩, true⟩

def state01 : KState := ⟨⟨362486891653559154, 362486953020233255⟩, ⟨(-94316587771534964), (-91642738005651812)⟩, true⟩

def words00 : List Nat := [371285531684608039, 371285531747852487, 371285531810886632, 371285531874678288, 371285531926913560, 371285531929343212, 371285532065640315, 371285532243744473, 371285532420565720, 371285532444858426]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 64500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 64500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362497236870455285, 362497298257029136⟩, ⟨(-761697168378252260), (-759022034783763404)⟩, true⟩

def words01 : List Nat := [371285532667520624, 371285532891415950, 371285533354321798, 371285533497796588, 371285533531139810, 371285533565126799, 371285533809477561, 371285533934993849, 371285534118852484, 371285534303668467]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 64510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 64500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362492165615485439, 362492227021876400⟩, ⟨(-434541204103474073), (-431864791810131143)⟩, true⟩

def words02 : List Nat := [371285534466043966, 371285534468239134, 371285534369933495, 371285534432076141, 371285534525810167, 371285534528058899, 371285534489597715, 371285534439630855, 371285534553953708, 371285534660192712]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 64520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 64500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362480336384634800, 362480397810796837⟩, ⟨328919412134182260, 331597100356634978⟩, true⟩

def words03 : List Nat := [371285534965511494, 371285535271711360, 371285535531070107, 371285535533266714, 371285535566120337, 371285535620899350, 371285535797960648, 371285535800159978, 371285535741966701, 371285535664846367]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 64530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 64500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362482375846684259, 362482437292501406⟩, ⟨197349656666517697, 200028613530097865⟩, true⟩

def words04 : List Nat := [371285535725262458, 371285535760549367, 371285535929392542, 371285536099150642, 371285536241471361, 371285536243667967, 371285536096904004, 371285536050794484, 371285536106856454, 371285536109132392]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 64540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 64500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362491968992467615, 362492030458308767⟩, ⟨(-421899235786850208), (-419218986272664564)⟩, true⟩

def words05 : List Nat := [371285536062768664, 371285536016683162, 371285536161114463, 371285536291043908, 371285536493053444, 371285536695877748, 371285536895410319, 371285536897617504, 371285536976836127, 371285537080166039]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 64550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 64500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362485374826358394, 362485436311786762⟩, ⟨3823356815555090, 6504870983042300⟩, true⟩

def words06 : List Nat := [371285537238944168, 371285537241145611, 371285537152660449, 371285537064421634, 371285536975365425, 371285536924115430, 371285536866529285, 371285536959344734, 371285537050878619, 371285537053167946]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 64560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 64500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362509140789351039, 362509202294586374⟩, ⟨(-1530890413861754003), (-1528207620656513489)⟩, true⟩

def words07 : List Nat := [371285537209464965, 371285537368424392, 371285537725422944, 371285537794282154, 371285537796031222, 371285537786594319, 371285538004113688, 371285538133249530, 371285538501171968, 371285538870039580]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 64570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 64500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362488042618787823, 362488104143879738⟩, ⟨(-168294244977485496), (-165610169337209272)⟩, true⟩

def words08 : List Nat := [371285539184056422, 371285539301153711, 371285539510933120, 371285539721902289, 371285540004674594, 371285540009127339, 371285540012599371, 371285540016793401, 371285540119553493, 371285540161756266]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 64580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 64500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362476060076823879, 362476121621732095⟩, ⟨605804053525300064, 608489409200571438⟩, true⟩

def words09 : List Nat := [371285540442567873, 371285540724309664, 371285541005304642, 371285541007502497, 371285541002113174, 371285541037795374, 371285541230221355, 371285541232419380, 371285541105740297, 371285540962431795]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 64590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 64500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 64500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk645
