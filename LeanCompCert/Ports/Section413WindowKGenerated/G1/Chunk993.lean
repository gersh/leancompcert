import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk993

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362483412356330418, 362483562699210491⟩, ⟨167880429377287271, 177959648406214077⟩, true⟩

def state01 : KState := ⟨⟨362482369241781068, 362482519615776605⟩, ⟨271513059245915677, 281595368202377059⟩, true⟩

def words00 : List Nat := [371285354905156217, 371285354917977153, 371285354928768478, 371285354940770266, 371285354981937740, 371285354985824826, 371285355032718676, 371285355092275211, 371285355130924186, 371285355134538083]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 99300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 99300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362498949601708052, 362499100007293857⟩, ⟨(-1375153311257711137), (-1365067864911737767)⟩, true⟩

def words01 : List Nat := [371285355165313587, 371285355226498245, 371285355360264125, 371285355416285184, 371285355454638261, 371285355494086983, 371285355633504967, 371285355723760477, 371285355864527219, 371285356006881943]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 99310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 99300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362486796506493907, 362486946943618387⟩, ⟨(-168093218070095458), (-158004639148771362)⟩, true⟩

def words02 : List Nat := [371285356147760690, 371285356169217596, 371285356231152226, 371285356294859897, 371285356370855498, 371285356374346645, 371285356315385776, 371285356261431106, 371285356235426866, 371285356255523545]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 99320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 99300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362471941906124170, 362472092374596674⟩, ⟨1307532582759713361, 1317624275645791749⟩, true⟩

def words03 : List Nat := [371285356337959775, 371285356421786731, 371285356504635613, 371285356508127508, 371285356455691641, 371285356435557220, 371285356415276302, 371285356418768298, 371285356287955291, 371285356158325744]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 99330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 99300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362481344041295149, 362481494541028965⟩, ⟨373475968576192140, 383570767121699022⟩, true⟩

def words04 : List Nat := [371285356027191800, 371285355947732029, 371285355816222027, 371285355764186844, 371285355710953214, 371285355634347834, 371285355459622721, 371285355388042140, 371285355340299011, 371285355343918968]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 99340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 99300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362486891333152573, 362487041864831727⟩, ⟨(-177677319474756042), (-167579347012303046)⟩, true⟩

def words05 : List Nat := [371285355307745357, 371285355255338189, 371285355235513485, 371285355239366166, 371285355254502713, 371285355277803378, 371285355299865607, 371285355303420671, 371285355272767926, 371285355294175109]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 99350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 99300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362478083234929166, 362478233797658821⟩, ⟨697537865921546484, 707638923727385876⟩, true⟩

def words06 : List Nat := [371285355399168317, 371285355402661187, 371285355372907511, 371285355325116564, 371285355276069115, 371285355212326920, 371285355096502875, 371285355083445340, 371285355069201412, 371285355050790827]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 99360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 99300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362495110339939775, 362495260934262501⟩, ⟨(-994507644675577755), (-984403447307318373)⟩, true⟩

def words07 : List Nat := [371285355011136822, 371285355045014404, 371285355160832183, 371285355187029040, 371285355196765877, 371285355207633036, 371285355318323033, 371285355380034521, 371285355482117905, 371285355585681713]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 99370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 99300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362488066070473965, 362488216696300574⟩, ⟨(-294443770228495311), (-284336441843723773)⟩, true⟩

def words08 : List Nat := [371285355683452078, 371285355698362043, 371285355755235111, 371285355813947980, 371285355868272657, 371285355871830426, 371285355855758030, 371285355839729664, 371285355876921569, 371285355909691689]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 99380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 99300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362484512778282952, 362484663435668360⟩, ⟨58769349945248167, 68879815115385063⟩, true⟩

def words09 : List Nat := [371285356042103870, 371285356175986939, 371285356288954063, 371285356292448240, 371285356271761845, 371285356277447745, 371285356382542687, 371285356391874903, 371285356394493436, 371285356391554833]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 99390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 99300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 99300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk993
