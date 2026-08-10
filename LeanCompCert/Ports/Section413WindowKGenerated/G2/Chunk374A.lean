import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk374A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360655409416441142, 360655417985263959⟩, ⟨(-2763247963418080853), (-2763031332461579927)⟩, true⟩

def state01 : KState := ⟨⟨360636216583475076, 360636225157100644⟩, ⟨(-2045641742085121474), (-2045424931482147118)⟩, true⟩

def words00 : List Nat := [360581543499249790, 360581544168573574, 360581545387471605, 360581546606457215, 360581547641353023, 360581548224447354, 360581548334841216, 360581548445292758, 360581549269556971, 360581550731624658]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 37400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 37400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360557034644805333, 360557043223176882⟩, ⟨916998943659794100, 917215931834281878⟩, true⟩

def words01 : List Nat := [360581552005326976, 360581553279054368, 360581554196741074, 360581554918250277, 360581555154382828, 360581555390628995, 360581555554340121, 360581555554844685, 360581555260171453, 360581554605641722]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 37410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 37400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360591749801134967, 360591758384275993⟩, ⟨(-382088414379820955), (-381871247708539819)⟩, true⟩

def words02 : List Nat := [360581553951033430, 360581553976275200, 360581555034979253, 360581556093723330, 360581556542658049, 360581556543162549, 360581556280663290, 360581556229978562, 360581556179155885, 360581556379314637]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 37420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 37400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360558656123626108, 360558664711574976⟩, ⟨856777044118170281, 856994390771119891⟩, true⟩

def words03 : List Nat := [360581556379768197, 360581556297498477, 360581556215139524, 360581556235405555, 360581556316393120, 360581556397467597, 360581556397917077, 360581556119456967, 360581555129826993, 360581554519020786]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 37430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 37400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360584048774634406, 360584057367341464⟩, ⟨(-94134537766031437), (-93917012943058703)⟩, true⟩

def words04 : List Nat := [360581554009426164, 360581554009930921, 360581553639115692, 360581552723911864, 360581551808670218, 360581550710393304, 360581550003656900, 360581550006849164, 360581550007304352, 360581549636895200]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 37440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 37400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk374A
