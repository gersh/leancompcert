import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk065

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨361093183309314434, 361093183529223630⟩, ⟨(-3360097101388180149), (-3360096131721399709)⟩, true⟩

def state01 : KState := ⟨⟨360750672162972024, 360750672383597980⟩, ⟨(-1133621152755380130), (-1133620178426026092)⟩, true⟩

def words00 : List Nat := [360576387003416280, 360576425615316038, 360576463108240198, 360576500589657648, 360576531870649237, 360576539962987519, 360576539963055265, 360576535685255510, 360576537179451693, 360576563924309695]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 6500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 6500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360201825314996576, 360201825536332269⟩, ⟨2442900881129932528, 2442901860083281844⟩, true⟩

def words01 : List Nat := [360576597501163434, 360576631067721112, 360576649121761842, 360576649121837232, 360576644041364567, 360576632835953633, 360576621633960190, 360576602976863595, 360576561210450181, 360576503735731546]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 6510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 6500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360559891699876581, 360559891921924752⟩, ⟨106441296794080902, 106442280396382020⟩, true⟩

def words02 : List Nat := [360576446278623678, 360576412168937582, 360576389906874583, 360576370199548269, 360576350498256102, 360576310292158384, 360576264730131583, 360576232863012524, 360576201005633218, 360576192424282545]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 6520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 6500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360573784046088490, 360573784268857804⟩, ⟨15444896397797411, 15445884712676547⟩, true⟩

def words03 : List Nat := [360576189928484767, 360576169181950867, 360576148441753893, 360576151650165051, 360576156045764788, 360576160440032133, 360576160440099563, 360576152997795709, 360576146386024095, 360576146024930079]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 6530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 6500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360432299736247199, 360432299959729462⟩, ⟨940986462202054592, 940987455183262922⟩, true⟩

def words04 : List Nat := [360576157646361564, 360576157646437289, 360576146713550132, 360576123862269994, 360576101017962082, 360576053377566595, 360576017442044643, 360576004631614343, 360575991825088069, 360575962166627671]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 6540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 6500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360691174856042233, 360691175080242828⟩, ⟨(-755485250787974095), (-755484253098140963)⟩, true⟩

def words05 : List Nat := [360575941411865468, 360575942586582285, 360575966852035341, 360575980752795965, 360575980752866212, 360575973714285376, 360575973662103675, 360575992239257110, 360576009797679697, 360576027350765898]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 6550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 6500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360824212848312623, 360824213073238448⟩, ⟨(-1630056041021087746), (-1630055038570188386)⟩, true⟩

def words06 : List Nat := [360576033284975547, 360576033285051805, 360576055750371167, 360576078481583133, 360576086467546882, 360576098789385552, 360576098789453882, 360576093957316505, 360576107283414427, 360576145041193069]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 6560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 6500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360879191640580120, 360879191866225373⟩, ⟨(-1991327885411193735), (-1991326878230108103)⟩, true⟩

def words07 : List Nat := [360576205766564815, 360576266473473808, 360576309251788767, 360576343692539950, 360576371190788780, 360576398680695453, 360576449111060258, 360576512602019522, 360576558601976495, 360576604587965214]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 6570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 6500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨361027780661489855, 361027780887855058⟩, ⟨(-2969005668255521726), (-2969004656333482366)⟩, true⟩

def words08 : List Nat := [360576673487932188, 360576753798253968, 360576844346093872, 360576934866446930, 360577005697772220, 360577066703332955, 360577126660759380, 360577186600008394, 360577249073461407, 360577317429148719]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 6580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 6500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360997877596008401, 360997877823101792⟩, ⟨(-2771943026326656934), (-2771942009602231384)⟩, true⟩

def words09 : List Nat := [360577371297462776, 360577425149443770, 360577487532246621, 360577568596439119, 360577643676658442, 360577718734128415, 360577782090379166, 360577822964700602, 360577886609438138, 360577950234917846]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 6590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 6500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 6500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk065
