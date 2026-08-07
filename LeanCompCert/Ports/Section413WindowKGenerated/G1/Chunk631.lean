import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk631

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362473715757144262, 362473774368857387⟩, ⟨732250650418692079, 734748712122647125⟩, true⟩

def state01 : KState := ⟨⟨362485823826517949, 362485882457411676⟩, ⟨(-31763867547418250), (-29264595449038944)⟩, true⟩

def words00 : List Nat := [371285418416804458, 371285418419177531, 371285418551187903, 371285418744389867, 371285418869820478, 371285418871964204, 371285418688696788, 371285418634912432, 371285418747453015, 371285418757019526]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 63100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 63100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362492195435112525, 362492254085585233⟩, ⟨(-433870441592929788), (-431369933768780330)⟩, true⟩

def words01 : List Nat := [371285418771717685, 371285418787202907, 371285419052803564, 371285419207944610, 371285419409042656, 371285419610930393, 371285419813593237, 371285419848719875, 371285419958473833, 371285420069429457]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 63110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 63100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362482803673288147, 362482862342860873⟩, ⟨158986780140149749, 161488493655690965⟩, true⟩

def words02 : List Nat := [371285420297179665, 371285420299325143, 371285420236278984, 371285420165747820, 371285420094418400, 371285420080143331, 371285420122550916, 371285420270867165, 371285420371586972, 371285420373807423]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 63120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 63100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362496011152508601, 362496069841472556⟩, ⟨(-674878334211520980), (-672375396429995584)⟩, true⟩

def words03 : List Nat := [371285420545173253, 371285420758139616, 371285421026428840, 371285421028573632, 371285420962718471, 371285420834543425, 371285420757040747, 371285420759410589, 371285420878041983, 371285421049143800]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 63130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 63100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362482263340200225, 362482322048485358⟩, ⟨193181674761550341, 195685832581632619⟩, true⟩

def words04 : List Nat := [371285421220581652, 371285421222727020, 371285421177020427, 371285421269090429, 371285421425074371, 371285421427219758, 371285421249127590, 371285421014331526, 371285420792394662, 371285420794844529]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 63140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 63100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362477713614291700, 362477772341912354⟩, ⟨480571151716913855, 483076530675100885⟩, true⟩

def words05 : List Nat := [371285420826412384, 371285420907937506, 371285420986715860, 371285420988909287, 371285420920127903, 371285420874471806, 371285421005992839, 371285421008141826, 371285420917367884, 371285420798699484]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 63150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 63100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362483446102539550, 362483504849404966⟩, ⟨118515503025694541, 121022097577152611⟩, true⟩

def words06 : List Nat := [371285420679086440, 371285420662384491, 371285420713342780, 371285420853954768, 371285420955377437, 371285420957523501, 371285420724761750, 371285420629901301, 371285420663196999, 371285420665418535]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 63160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 63100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362482417829215422, 362482476595616732⟩, ⟨183474323299710487, 185982152030223563⟩, true⟩

def words07 : List Nat := [371285420636710491, 371285420610269007, 371285420682459272, 371285420684824205, 371285420661082778, 371285420648785927, 371285420635745230, 371285420622351976, 371285420326652278, 371285420282733387]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 63170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 63100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362473409131294214, 362473467916831058⟩, ⟨752717736031312321, 755226773844746667⟩, true⟩

def words08 : List Nat := [371285420297212272, 371285420299396208, 371285420152695494, 371285420005876756, 371285419858196792, 371285419787382913, 371285419618386656, 371285419648157799, 371285419649810694, 371285419598645345]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 63180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 63100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362497935841668825, 362497994646638264⟩, ⟨(-797268679710759374), (-794758413854370220)⟩, true⟩

def words09 : List Nat := [371285419410967188, 371285419410160621, 371285419568813011, 371285419570964618, 371285419475351187, 371285419301652670, 371285419201419726, 371285419203807721, 371285419352833739, 371285419554252790]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 63190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 63100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 63100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk631
