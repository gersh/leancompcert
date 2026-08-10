import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk588A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360596741125764911, 360596763102254725⟩, ⟨(-865462389458360863), (-864589374026853057)⟩, true⟩

def state01 : KState := ⟨⟨360577607175296018, 360577629159515835⟩, ⟨259697165213881696, 260570635207934080⟩, true⟩

def words00 : List Nat := [360582059930064562, 360582060120384769, 360582060121118396, 360582060111701674, 360582060102152514, 360582060029100861, 360582060029777035, 360582060028129237, 360582060026391744, 360582059879379939]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 58800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 58800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360608530399250797, 360608552391223363⟩, ⟨(-1559078982877915015), (-1558205056906030607)⟩, true⟩

def words01 : List Nat := [360582059863944014, 360582059924089539, 360582060200150574, 360582060483737212, 360582060521225968, 360582060558770565, 360582060639099072, 360582060863891422, 360582061314938638, 360582061766159083]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 58810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 58800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360589004698990027, 360589026698799055⟩, ⟨(-410663228192442426), (-409788841242367620)⟩, true⟩

def words02 : List Nat := [360582061996915432, 360582061997737175, 360582062073425541, 360582062207619851, 360582062208311555, 360582062178870775, 360582061951658575, 360582061579317554, 360582061206811899, 360582061173119697]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 58820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 58800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360570126963683379, 360570148971227245⟩, ⟨700085568382807821, 700960410412595715⟩, true⟩

def words03 : List Nat := [360582061581089081, 360582061989202148, 360582062251085205, 360582062382290112, 360582062382990054, 360582062273216912, 360582062163208174, 360582062163446483, 360582062164183493, 360582061962566685]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 58830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 58800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360590021755943656, 360590043771254741⟩, ⟨(-470602345039666085), (-469727045948865561)⟩, true⟩

def words04 : List Nat := [360582061760770978, 360582061882266180, 360582062145252182, 360582062408385649, 360582062427226864, 360582062428048925, 360582062158781407, 360582062110628380, 360582062062247554, 360582062138895922]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 58840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 58800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk588A
