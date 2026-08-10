import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk325A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360542846833755781, 360542853229835189⟩, ⟨1253296112628857686, 1253436672448400026⟩, true⟩

def state01 : KState := ⟨⟨360563112218037429, 360563118618213092⟩, ⟨594617924171726538, 594758617139732160⟩, true⟩

def words00 : List Nat := [360581419325771839, 360581418113766572, 360581417592707522, 360581417804289092, 360581417804691292, 360581417107042225, 360581415464153913, 360581414764984118, 360581414065718499, 360581413254237077]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 32500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 32500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360520438723908101, 360520445128208502⟩, ⟨1982107584734148539, 1982248411818475793⟩, true⟩

def words01 : List Nat := [360581412691901940, 360581411656168478, 360581410620417759, 360581409439865830, 360581408738427967, 360581407380132619, 360581406021874244, 360581404187335934, 360581401750360110, 360581399876419403]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 32510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 32500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360524571271658379, 360524577680051029⟩, ⟨1847761217716620436, 1847902177900964504⟩, true⟩

def words02 : List Nat := [360581398002451562, 360581396443315107, 360581395274041513, 360581393500934012, 360581391727865147, 360581389707440363, 360581388296459366, 360581387031352169, 360581385766281210, 360581383772209067]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 32520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 32500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360598248307524837, 360598254720012106⟩, ⟨(-549354611107766707), (-549213517705209881)⟩, true⟩

def words03 : List Nat := [360581382026345904, 360581381222880047, 360581380557597265, 360581380558031157, 360581379753296193, 360581378138932540, 360581376524577629, 360581376096090319, 360581376615146822, 360581377134267808]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 32530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 32500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360526572690243406, 360526579106868093⟩, ⟨1783128976118602565, 1783270204172853419⟩, true⟩

def words04 : List Nat := [360581377180371420, 360581377180805523, 360581376629643864, 360581376052478963, 360581375475230966, 360581374406402657, 360581372394968343, 360581369795281215, 360581367195673155, 360581364673816568]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 32540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 32500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk325A
