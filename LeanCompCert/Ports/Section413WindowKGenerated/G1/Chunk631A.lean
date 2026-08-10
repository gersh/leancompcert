import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk631A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk631A
