/*
 * Copyright (c) 2004-2006 The Regents of The University of Michigan
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met: redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer;
 * redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution;
 * neither the name of the copyright holders nor the names of its
 * contributors may be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#include "cpu/pred/2bit_local.hh"

#include "base/intmath.hh"
#include "base/logging.hh"
#include "base/trace.hh"
#include "debug/Fetch.hh"

LocalBP::LocalBP(const LocalBPParams *params)
    : BPredUnit(params),
      localPredictorSize(params->localPredictorSize),
      localCtrBits(params->localCtrBits),
      localPredictorSets(localPredictorSize / localCtrBits),
      localCtrs(localPredictorSets, SatCounter(localCtrBits)),
      indexMask(localPredictorSets - 1)
{
    if (!isPowerOf2(localPredictorSize)) {
        fatal("Invalid local predictor size!\n");
    }

    if (!isPowerOf2(localPredictorSets)) {
        fatal("Invalid number of local predictor sets! Check localCtrBits.\n");
    }

    DPRINTF(Fetch, "index mask: %#x\n", indexMask);

    DPRINTF(Fetch, "local predictor size: %i\n",
            localPredictorSize);

    DPRINTF(Fetch, "local counter bits: %i\n", localCtrBits);

    DPRINTF(Fetch, "instruction shift amount: %i\n",
            instShiftAmt);

    initialize_W(size_branch_record,size_global_his_record,size_global_his);

    for(int i = 0; i < size_global_his; i++){
        branch_history_buf.push_back(0);
        GHR_reserve.push_back(0);
        history_done.push_back(true);
    }
    for(int i = 0; i < size_global_his; i++){
        address_branch_history_buf.push_back(0);
        GA_reserve.push_back(0);
    }
}

void
LocalBP::btbUpdate(ThreadID tid, Addr branch_addr, void * &bp_history)
{
// Place holder for a function that is called to update predictor history when
// a BTB entry is invalid or not found.
}


bool
LocalBP::lookup(ThreadID tid, Addr instPC, void * &bp_history)
{
    bool taken;

    uint64_t cur_addr = static_cast<uint64_t>(instPC);

    num_prediction++;

    taken = getPrediction(cur_addr,address_branch_history_buf, branch_history_buf);
    std::cout<<"Add:"<<instPC<<"("<<cur_addr<<") prediction: "<<num_prediction<<" is: "<<taken<<std::endl;
    std::cout<<"buf aft prediction:\n";
    show_buf();

    // write_acc();
    return taken;
}

void
LocalBP::update(ThreadID tid, Addr branch_addr, bool taken, void *bp_history,
                bool squashed, const StaticInstPtr & inst, Addr corrTarget)
{
    assert(bp_history == NULL);
    std::cout<<"tid:"<<tid<<" update("<<branch_addr<<"to "<<corrTarget<<")="<<taken<<" squashed="<<squashed<<std::endl;
    //if squash wrong
    if (squashed) {
        num_prediction--;
        address_branch_history_buf.assign(GA_reserve.begin(),GA_reserve.end());
        branch_history_buf.assign(GHR_reserve.begin(),GHR_reserve.end());
        history_done[0] = true;
        return;
    }else{
      if((taken!=branch_history_buf[0]) && (history_done[0]==false)){
        std::cout<<"Prediction: "<<num_prediction<<" prediction: "<<branch_history_buf[0]<<" outcome: "<<taken<<std::endl;
        show_buf();
        num_wrong_prediction++;

        int index_1d = branch_addr%size_1d;

        int length_GA = GHR_reserve.size();
        
        if(taken == true){
          if(W[index_1d][0][0] > weight_threshold_max){
            //over threshold, do not add
          }else{
            W[index_1d][0][0] = W[index_1d][0][0] + 1;
          }
            
        }else{
          if(W[index_1d][0][0] < weight_threshold_min){
            //over threshold, do not sub
          }else{
            W[index_1d][0][0] = W[index_1d][0][0] - 1;
          }
            
        }

        for(int ibr = 0; ibr < length_GA ; ibr++){
          int index_2d = GA_reserve[ibr]%size_2d + 1;
          int index_3d = (ibr)%(size_3d) + 1;
          if(GHR_reserve[ibr]==taken){
            // std::cout<<"GHR: "<<GHR_reserve[ibr]<<" taken:"<<taken<<std::endl;
            if(W[index_1d][index_2d][index_3d] > weight_threshold_max){
              //over threshold, do not add
            }else{
              W[index_1d][index_2d][index_3d] = W[index_1d][index_2d][index_3d] + 1;
            }
          }else{
            if(W[index_1d][index_2d][index_3d] < weight_threshold_min){
              //over threshold, do not sub
            }else{
              W[index_1d][index_2d][index_3d] = W[index_1d][index_2d][index_3d] - 1;
            }
          }
        }
        // show_W();
        if (taken == true) {
            DPRINTF(Fetch, "Branch updated as taken.\n");
            branch_history_buf[0] = true;
            history_done[0] = true;
            GA_reserve.pop_back();
            GA_reserve.insert(GA_reserve.begin(),branch_addr);
            GHR_reserve.pop_back();
            GHR_reserve.insert(GHR_reserve.begin(),true);
        } else {
            DPRINTF(Fetch, "Branch updated as not taken.\n");
            branch_history_buf[0] = false;
            history_done[0] = true;
            GA_reserve.pop_back();
            GA_reserve.insert(GA_reserve.begin(),branch_addr);
            GHR_reserve.pop_back();
            GHR_reserve.insert(GHR_reserve.begin(),false);
        }
      }else if((taken==branch_history_buf[0]) && (history_done[0]==false)){
        // just update GHR and GA
        GA_reserve.assign(address_branch_history_buf.begin(),address_branch_history_buf.end());
        GHR_reserve.assign(branch_history_buf.begin(),branch_history_buf.end());
        history_done[0] = true;
      }
    }

}

inline bool LocalBP::getPrediction(uint64_t cur_branch_addr, std::vector<uint64_t> &GA, std::vector<bool> &GHR)
{ 

  bool taken = false;
  // write algorithm here
  int index_1d = cur_branch_addr%size_1d;

  int32_t predict_weight = 0;
    
  predict_weight = W[index_1d][0][0];

  int length_GA = GA.size();

  if(length_GA>0){
    for(int ibr = 0; ibr < length_GA ; ibr++){
      int index_2d = GA[ibr]%size_2d + 1;
      int index_3d = (ibr)%(size_3d) + 1;
      if(GHR[ibr]==true){
        predict_weight = predict_weight + W[index_1d][index_2d][index_3d];
      }else{
        predict_weight = predict_weight - W[index_1d][index_2d][index_3d];
      }      
    }
  }
  // std::cout<<"prediction weight: "<<predict_weight<<std::endl;
  if(predict_weight > -1){
    taken = true;
  }

  GA.pop_back();
  GA.insert(GA.begin(),cur_branch_addr);

  history_done.pop_back();
  history_done.insert(history_done.begin(),false);

  GHR.pop_back();
  GHR.insert(GHR.begin(),taken);

  return taken;

}

inline
unsigned
LocalBP::getLocalIndex(Addr &branch_addr)
{
    uint32_t index_1d = branch_addr%size_1d;
    // uint32_t index_2d = GA[ibr]%size_2d + 1;
    // uint32_t index_3d = (ibr)%(size_3d) + 1;
    return (index_1d);
}

void
LocalBP::uncondBranch(ThreadID tid, Addr pc, void *&bp_history)
{
}

LocalBP*
LocalBPParams::create()
{
    return new LocalBP(this);
}


void LocalBP::initialize_W(uint32_t d1st, uint32_t d2nd, uint32_t d3rd){

  std::vector<int32_t> position_global_history;
  std::vector<std::vector<int32_t>> global_history;

  size_1d = d1st;
  size_2d = d2nd;
  size_3d = d3rd;

  for(uint32_t k = 0 ; k < d3rd + 1 ; k++){
    position_global_history.push_back(0);
  }
  for(uint32_t j = 0 ; j < d2nd + 1 ; j++){
    global_history.push_back(position_global_history);
  }
  for(uint32_t i = 0 ; i < d1st ; i++){
    W.push_back(global_history);
  }
}

void LocalBP::write_log(){

  std::ofstream out;
  std::ofstream out_addr;

  out.open("./buf_history.txt",std::ios_base::app);
  out_addr.open("./buf_history_addr.txt",std::ios_base::app);

  int length = branch_history_buf.size();
  int length_addr = address_branch_history_buf.size();

  out<<"fail: "<<num_wrong_prediction<<" =>";

  for(int i=0;i<length;i++){
    out<<branch_history_buf[i]<<" ";
  }
  out<<std::endl;
  
  for(int i=0;i<length_addr;i++){
    out_addr<<address_branch_history_buf[i]<<" ";
  }
  out_addr<<std::endl;

  out.close();
  out_addr.close();
}

void LocalBP::write_acc(){
  std::ofstream out("./pred_acc.txt");
  out<<"Pred: "<<num_prediction;
  out<<" fail: "<<num_wrong_prediction;
  out<<std::endl;
}

void LocalBP::show_W(){

  for(int i = 0 ; i < size_1d; i++){ 
    std::cout<<"i = "<<i<<std::endl;
    for(int j = 0 ; j < size_2d + 1; j++){
      for(int k = 0 ; k < size_3d + 1; k++){
        std::cout<<"("<<i<<","<<j<<","<<k<<") = "<< W[i][j][k] <<" ";
      }
      std::cout<<"\n";
    }
  }

}

void LocalBP::show_buf(){
  for(int i = 0 ; i < branch_history_buf.size(); i++){ 
    std::cout<<"("<<i<<") = "<< branch_history_buf[i] <<" ";
  }
  std::cout<<"\n";
  for(int i = 0 ; i < address_branch_history_buf.size(); i++){ 
    std::cout<<"("<<i<<") = "<< address_branch_history_buf[i] <<" ";
  }
  std::cout<<"\nGHReserve => ";
  for(int i = 0 ; i < GHR_reserve.size(); i++){ 
    std::cout<<"("<<i<<") = "<< GHR_reserve[i] <<" ";
    
  }
  std::cout<<"\n";
}