import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk259A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360530975950334154, 360530979934016694⟩, ⟨1353205049082596561, 1353274843733385321⟩, true⟩

def state01 : KState := ⟨⟨360556517813457534, 360556521800341411⟩, ⟨691725937212540912, 691795814794172036⟩, true⟩

def words00 : List Nat := [360583227910961501, 360583226853276793, 360583227764173982, 360583228963198378, 360583228963513339, 360583228650154144, 360583226852598525, 360583225014159479, 360583223175763683, 360583221754598230]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 25900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 25900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360564912029800003, 360564916019918706⟩, ⟨474228404608732087, 474298366020998061⟩, true⟩

def words01 : List Nat := [360583220724454899, 360583218956054016, 360583217187724760, 360583217776363007, 360583217974404183, 360583218172488441, 360583218172791141, 360583217464683184, 360583215273589569, 360583214567990504]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 25910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 25900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360512291276538913, 360512295269860202⟩, ⟨1838320953744468112, 1838390998183830818⟩, true⟩

def words02 : List Nat := [360583213862335262, 360583212704272662, 360583211140414976, 360583208824381810, 360583206508473239, 360583203191699083, 360583200854835447, 360583198736990538, 360583196619269160, 360583193495783220]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 25920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 25900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360608529104151766, 360608533100679687⟩, ⟨(-657701620052569618), (-657631492449367982)⟩, true⟩

def words03 : List Nat := [360583190761947383, 360583189512180505, 360583188496107675, 360583188496447395, 360583187249309808, 360583184757033474, 360583182264884699, 360583180604756801, 360583181076717747, 360583182054364998]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 25930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 25900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360587446274667201, 360587450274437215⟩, ⟨(-110654708173672837), (-110584496454644499)⟩, true⟩

def words04 : List Nat := [360583182280874130, 360583183190273373, 360583185582119415, 360583187973880886, 360583189984393683, 360583190514622790, 360583190514929083, 360583190225598465, 360583189936230361, 360583188993698337]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 25940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 25900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk259A
