import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk049

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨359970420367374555, 359970420488664216⟩, ⟨2965798204837101613, 2965798608357862005⟩, true⟩

def state01 : KState := ⟨⟨360371900210766250, 360371900332577700⟩, ⟨996278517822734097, 996278923902902613⟩, true⟩

def words00 : List Nat := [360575562012552981, 360575437877951146, 360575341202921080, 360575285544201617, 360575229908172906, 360575140163333915, 360575048222699790, 360574954638619001, 360574861092649851, 360574808463718821]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 4900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 4900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360288586697097765, 360288586819436780⟩, ⟨1405798111477990420, 1405798520151077436⟩, true⟩

def words01 : List Nat := [360574767146698102, 360574705358087087, 360574643594618833, 360574596265909736, 360574582528297483, 360574557858180733, 360574533198092924, 360574475155231216, 360574376313204046, 360574318225971552]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 4910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 4900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360128406096357165, 360128406219220026⟩, ⟨2193399026325770159, 2193399437578822471⟩, true⟩

def words02 : List Nat := [360574260162329851, 360574180814123242, 360574087377129869, 360573972089446144, 360573856848570815, 360573730029139359, 360573624678998042, 360573529745202686, 360573434849920625, 360573314827248185]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 4920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 4900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360469033183462605, 360469033306850975⟩, ⟨512590384568639890, 512590798415109034⟩, true⟩

def words03 : List Nat := [360573224600441130, 360573174953607248, 360573125326885290, 360573116247450554, 360573066611172949, 360572978768756839, 360572890961915564, 360572843659900619, 360572817635283579, 360572796626368204]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 4930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 4900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360247335040684923, 360247335164606011⟩, ⟨1608506064677961442, 1608506481158619740⟩, true⟩

def words04 : List Nat := [360572775625948976, 360572730841851251, 360572689092361810, 360572687732264816, 360572686372703457, 360572658914910155, 360572591124785233, 360572491445165267, 360572391805818257, 360572285968880480]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 4940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 4900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360048955034519199, 360048955158966995⟩, ⟨2592176588005751575, 2592177007096294909⟩, true⟩

def words05 : List Nat := [360572220335557979, 360572195011816468, 360572169698294765, 360572117337839327, 360572024752342805, 360571921325140454, 360571817939650778, 360571754795600570, 360571676878428404, 360571571491042861]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 4950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 4900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360450981104756593, 360450981229734398⟩, ⟨594411416559723027, 594411838281780865⟩, true⟩

def words06 : List Nat := [360571466146131525, 360571356002769742, 360571266862948846, 360571175990003915, 360571085153659882, 360570959012555503, 360570824443266107, 360570729978451543, 360570635551641855, 360570581197195521]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 4960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 4900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360428881063404698, 360428881188916927⟩, ⟨704759508166533760, 704759932547387984⟩, true⟩

def words07 : List Nat := [360570557137706757, 360570512872431110, 360570468624946764, 360570480871208015, 360570486379746391, 360570491886080249, 360570491886131594, 360570466201391305, 360570427670585838, 360570399247661383]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 4970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 4900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360442578896489360, 360442579022531429⟩, ⟨635756823838475212, 635757250860648672⟩, true⟩

def words08 : List Nat := [360570370836131351, 360570354463788350, 360570320142302413, 360570253972047213, 360570187828329733, 360570110899706396, 360570054680494226, 360570038217402231, 360570021760903848, 360569985285228954]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 4980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 4900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360798931939805656, 360798932066381238⟩, ⟨(-1145687494131680426), (-1145687064444635920)⟩, true⟩

def words09 : List Nat := [360569959758074023, 360569915862259072, 360569871984010587, 360569867778566811, 360569860925947817, 360569816495901460, 360569772083627241, 360569748816738227, 360569794653433925, 360569840471811225]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 4990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 4900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 4900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk049
