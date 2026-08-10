import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk650A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360581152792616506, 360581179862944124⟩, ⟨114003410155449166, 115192019676196994⟩, true⟩

def state01 : KState := ⟨⟨360569936060972061, 360569963140025095⟩, ⟨843122260561554281, 844311437277764327⟩, true⟩

def words00 : List Nat := [360582952021414234, 360582951860010032, 360582951785215371, 360582951866540704, 360582951888401588, 360582951889317180, 360582951675310347, 360582951325097795, 360582950974731607, 360582950548689574]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 65000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 65000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360561982326448730, 360562009414120308⟩, ⟨1360263128541087983, 1361452865592104823⟩, true⟩

def words01 : List Nat := [360582950386008590, 360582950423274286, 360582950424094026, 360582950313318769, 360582949966524625, 360582949560831863, 360582949154854732, 360582948924007035, 360582948721153006, 360582948400056822]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 65010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 65000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360594179907867699, 360594207004195949⟩, ⟨(-733526655214197227), (-732336355263835547)⟩, true⟩

def words02 : List Nat := [360582948078769198, 360582947696955300, 360582947433269547, 360582947162644803, 360582946891968233, 360582946393529381, 360582945931173634, 360582945705102073, 360582945487696111, 360582945661832095]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 65020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 65000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360587097061335767, 360587124166382488⟩, ⟨(-272855973765420746), (-271665106808966722)⟩, true⟩

def words03 : List Nat := [360582945700415065, 360582945739102780, 360582946013585395, 360582946407441303, 360582946741908101, 360582947076514193, 360582947212353684, 360582947213270510, 360582947272551613, 360582947337815754]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 65030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 65000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360593121660033396, 360593148773704042⟩, ⟨(-664731957696133577), (-663540529797126253)⟩, true⟩

def words04 : List Nat := [360582947591869549, 360582947767435713, 360582947768266064, 360582947763158615, 360582947757884600, 360582947779695924, 360582947993612338, 360582948207697313, 360582948303426414, 360582948461183142]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 65040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 65000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk650A
