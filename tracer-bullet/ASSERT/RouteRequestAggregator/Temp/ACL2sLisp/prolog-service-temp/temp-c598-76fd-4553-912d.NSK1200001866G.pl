:- module('c598-76fd-4553-912d.NSK1200001866G',[]).
targetVar(['_DummyVar']).
:- load_rdf_file('/C:/SadlWorkspace28/ReqAggregator-v4/OwlModels/RequestAggregator.owl').
:- load_rdf_file('/C:/SadlWorkspace28/ReqAggregator-v4/OwlModels/SadlBaseModel.owl').
:- load_rdf_file('/C:/SadlWorkspace28/ReqAggregator-v4/OwlModels/SadlImplicitModel.owl').
:- load_rdf_file('/C:/SadlWorkspace28/ReqAggregator-v4/OwlModels/SadlBuiltinFunctions.owl').
:- load_rdf_file('/C:/SadlWorkspace28/ReqAggregator-v4/OwlModels/test.owl').
:- load_rdf_file('/C:/SadlWorkspace28/ReqAggregator-v4/OwlModels/SadlListModel.owl').
:- load_pl_file('/C:/SadlWorkspace28/ReqAggregator-v4/OwlModels/SadlBuiltinFunctions.sadl.pl').

qresult([true]) :- stage2_translation('C:/SadlWorkspace28/ReqAggregator-v4/OwlModels/RA-Req2.sreq.pl','C:/SadlWorkspace28/ReqAggregator-v4/Temp/IntermediateForm/RA-Req2.sreq.pl').

