import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk509A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360598551185685574, 360598567462493170⟩, ⟨(-844010488528750707), (-843450681247073637)⟩, true⟩

def state01 : KState := ⟨⟨360590204560524102, 360590220844030716⟩, ⟨(-419297351374724851), (-418737203079919225)⟩, true⟩

def words00 : List Nat := [360581997121325824, 360581997122029888, 360581997137567981, 360581997303037693, 360581997372039065, 360581997372742643, 360581997056966786, 360581996508278301, 360581995959468577, 360581995957403467]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 50900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 50900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360546643914486009, 360546660204623945⟩, ⟨1798582634662591198, 1799143120591611694⟩, true⟩

def words01 : List Nat := [360581996106000438, 360581996254716961, 360581996255349583, 360581996209729753, 360581995779257634, 360581995112872730, 360581994446307884, 360581994036990718, 360581993637790700, 360581992944619853]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 50910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 50900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360594440551615896, 360594456848395360⟩, ⟨(-635509714132980523), (-634948889985338781)⟩, true⟩

def words02 : List Nat := [360581992251317939, 360581991672531223, 360581991458328917, 360581991544014818, 360581991544675706, 360581991238195443, 360581990547029110, 360581990156029971, 360581989764839928, 360581990003252219]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 50920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 50900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360559445618328084, 360559461921821568⟩, ⟨1147049900570229744, 1147611066696027758⟩, true⟩

def words03 : List Nat := [360581990054634169, 360581990106099283, 360581990299480117, 360581990733447586, 360581991003821740, 360581991274300029, 360581991351746037, 360581991352450006, 360581991045389576, 360581990603931816]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 50930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 50900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360532125871239135, 360532142181361649⟩, ⟨2538794430259608334, 2539355934101403806⟩, true⟩

def words04 : List Nat := [360581990162254392, 360581989762364483, 360581988977986886, 360581988000853673, 360581987023644851, 360581985840833696, 360581984956467306, 360581984186595640, 360581983416685531, 360581982337084935]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 50940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 50900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk509A
