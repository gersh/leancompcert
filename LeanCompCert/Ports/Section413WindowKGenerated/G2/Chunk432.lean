import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk432

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360571427717685733, 360571439285628247⟩, ⟨504213876270228828, 504551597797702642⟩, true⟩

def state01 : KState := ⟨⟨360591713199365654, 360591724772851206⟩, ⟨(-372294245045316695), (-371956284030140627)⟩, true⟩

def words00 : List Nat := [360583118716439813, 360583118717028994, 360583118449272940, 360583117911198785, 360583117373043303, 360583116696741964, 360583116547246792, 360583116740716807, 360583116741246554, 360583116865512100]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 43200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 43200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360623100353860291, 360623111932918098⟩, ⟨(-1728743697993971864), (-1728405496175429260)⟩, true⟩

def words01 : List Nat := [360583117050518449, 360583117235683720, 360583117804666160, 360583118484698845, 360583118670421305, 360583118856181406, 360583119289383872, 360583120134327691, 360583121060115173, 360583121985990091]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 43210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 43200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360597868204641069, 360597879789308134⟩, ⟨(-638294699967033884), (-637956255689076370)⟩, true⟩

def words02 : List Nat := [360583122641701859, 360583122763952356, 360583123421313847, 360583124078817628, 360583124274506512, 360583124275096032, 360583123937354324, 360583123330746607, 360583122724054065, 360583122872843351]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 43220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 43200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360560776861024737, 360560788451248719⟩, ⟨965389233980695531, 965727918512406833⟩, true⟩

def words03 : List Nat := [360583123391583668, 360583123910421815, 360583124159367487, 360583124159957120, 360583123875589438, 360583123453500923, 360583123143368965, 360583123143961410, 360583123100340386, 360583122584424307]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 43230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 43200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360612984187454576, 360612995783242248⟩, ⟨(-1292363375083950266), (-1292024449951010738)⟩, true⟩

def words04 : List Nat := [360583122068400733, 360583121633895433, 360583121701550935, 360583121935989555, 360583121936538722, 360583121729286561, 360583121696171582, 360583121855808047, 360583122384944293, 360583123076253947]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 43240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 43200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360584688980333741, 360584700581746329⟩, ⟨(-68521121698459844), (-68181953260958268)⟩, true⟩

def words05 : List Nat := [360583123436343465, 360583123796482316, 360583123982919082, 360583124460119349, 360583124673570030, 360583124887106919, 360583124887632479, 360583124831770251, 360583124484130573, 360583124521247012]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 43250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 43200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360564171483255822, 360564183090222290⟩, ⟨819183835121515531, 819523243848025181⟩, true⟩

def words06 : List Nat := [360583125092310956, 360583125321658575, 360583125322194488, 360583125087668529, 360583124853055722, 360583124305027309, 360583124024763882, 360583123721673290, 360583123418531764, 360583122846262226]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 43260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 43200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360633854693549415, 360633866306083970⟩, ⟨(-2196337338434453943), (-2195997688749134533)⟩, true⟩

def words07 : List Nat := [360583122505292770, 360583122602198670, 360583123118146791, 360583123915032203, 360583124246689807, 360583124578378043, 360583125062554979, 360583125814486555, 360583126987341149, 360583128160275206]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 43270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 43200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360642904228173496, 360642915846344348⟩, ⟨(-2588195195616873319), (-2587855301966252501)⟩, true⟩

def words08 : List Nat := [360583128904568790, 360583129773339028, 360583131175545146, 360583132577859444, 360583133630219568, 360583134443151228, 360583134945076081, 360583135447052313, 360583136328406647, 360583137709965742]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 43280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 43200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360588928998970673, 360588940622696224⟩, ⟨(-251183631532382167), (-250843497390298153)⟩, true⟩

def words09 : List Nat := [360583139624687637, 360583141539434242, 360583143185103223, 360583144299220245, 360583145049059119, 360583145799015728, 360583146832917787, 360583147335393202, 360583147469719665, 360583147604119510]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 43290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 43200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 43200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk432
