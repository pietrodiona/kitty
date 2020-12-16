/* kitty: C++ truth table library
 * Copyright (C) 2017-2020  EPFL
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use,
 * copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following
 * conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
 * HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 * WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 */

/*!
  \file threshold_identification.hpp
  \brief Threshold logic function identification

  \author CS-472 2020 Fall students
*/

#pragma once

#include <vector>
#include <lpsolve/lp_lib.h> /* uncomment this line to include lp_solve */
#include "traits.hpp"
#include <fstream>
#include "properties.hpp"
#include "isop.hpp"

namespace kitty
{
enum Constraint_Type_mine { GE_M = 2, LE_M = 1};
struct Constraint_mine
{
  std::vector<uint32_t> ws;
  Constraint_Type_mine type;
};



/*! \brief Threshold logic function identification

  Given a truth table, this function determines whether it is a threshold logic function (TF)
  and finds a linear form if it is. A Boolean function is a TF if it can be expressed as

  f(x_1, ..., x_n) = \sum_{i=1}^n w_i x_i >= T

  where w_i are the weight values and T is the threshold value.
  The linear form of a TF is the vector [w_1, ..., w_n; T].

  \param tt The truth table
  \param plf Pointer to a vector that will hold a linear form of `tt` if it is a TF.
             The linear form has `tt.num_vars()` weight values and the threshold value
             in the end.
  \return `true` if `tt` is a TF; `false` if `tt` is a non-TF.
*/
template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
bool is_threshold(const TT& tt, std::vector<int64_t>* plf = nullptr )
{
  auto ttstar = tt;
  int nvar = tt.num_vars();
  std::vector<int64_t> linear_form(nvar+1, 0);
  std::vector<bool> neg_un(nvar, false); //this vector saves the negativity of an unate

  /* TODO */
  /* STEP 1: check unateness*/
  for ( uint32_t i = 0u; i < nvar; i++ )
  {
    int res = check_unateness( ttstar, i );
    if ( res == 0 ){
      return false;
    }
    if ( res == -1 ){
      neg_un[i]=true;
      ttstar=flip( ttstar, i );
    }
  }

  /* Step 2: Create the LP model and solve it */
  std::vector<Constraint_mine> Cs;
  std::vector<double> row;

  std::vector<cube> on_set( isop( ttstar ) );

  for ( auto& c : on_set )
  {
    Constraint_mine C;
    for ( uint32_t i = 0 ; i < nvar; i++ )
    {
      if ( c.get_mask( i ) )
        C.ws.emplace_back( i+1 );
    }
    C.type = GE_M;
    Cs.emplace_back( C );
  }


  std::vector<cube> off_set( isop( unary_not(ttstar) ) );

  for ( auto& c : off_set )
  {
    Constraint_mine C;
    for ( uint32_t i( 0 ); i < nvar; i++ )
    {
      if ( !c.get_mask( i ) )
        C.ws.emplace_back( i+1 );
    }
    C.type = LE_M;
    Cs.emplace_back( C );
  }

  lprec* lp;

  /* Create a new LP model */
  lp = make_lp( 0, nvar+1 );
  if ( lp == nullptr )
  {
    fprintf( stderr, "Unable to create new LP model\n" );
    return false;
  }

  set_verbose( lp, IMPORTANT );

  set_add_rowmode( lp, TRUE);

  /* set the objective function row*/
  row.emplace_back(0.0);
  for ( uint32_t i = 1u; i< nvar+2 ; i++){
    row.emplace_back(1.0);
  }
  set_obj_fn(lp,row.data());
  /* set the constraints*/
  for(auto C : Cs){
    for ( uint32_t i = 0u; i< nvar+1 ; i++){
      row[i]=0.0;
    }
    row[nvar+1]=(-1.0);
    for(auto w : C.ws){
      row[w]=(1.0);
    }
    double t=0.0;
    if(C.type==LE_M){
      t=(-1.0);
    }
    if(C.type==GE_M){
      add_constraint(lp,row.data(),GE,t);
    }else{
      add_constraint(lp,row.data(),LE,t);
    }

  }

  for( uint32_t i = 1u ; i < nvar+2; i++ ){
    set_int(lp,i,TRUE);
  }

  for ( uint32_t i = 1u; i < nvar + 2; i++ )
  {
    for ( uint32_t j = 0u; j< nvar+2 ; j++){
      row[j]=0.0;
    }
    row[i]=1.0;
    add_constraint(lp,row.data(),GE,0.0);
  }

  set_add_rowmode( lp, FALSE);
  print_lp(lp);
  if( solve(lp)==INFEASIBLE ){
    return false;
  }


  double *sol;
  get_ptr_variables( lp, &sol );

  for ( uint32_t i = 0u; i < nvar + 1; i++ ){
    linear_form[i] = sol[i];
  }
  delete_lp( lp );

  /* Step 3 (optional): Recover the linear form f by f* */

  for ( uint32_t i = 0; i < nvar; i++ )
  {
    if ( neg_un[i] )
    {
      linear_form[nvar] = linear_form[nvar] - linear_form[i];
      linear_form[i] = -linear_form[i];
    }
  }

  /* if tt is TF: */
  /* push the weight and threshold values into `linear_form` */
  if ( plf )
  {
    *plf = linear_form;
  }
  return true;
}

/*!
  \brief Check whether the truth table is a positive, a negative or it is not a unate in a specified variable.

  This function check the unateness in the specified variable of a truth table.
  It returns -1 if it is a negative unate,
              0 if it is a binate,
              1 if it is a positive unate.

  \param tt the truth table
  \param i the variable it is wishable apply this function.
*/
template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
int check_unateness( TT& tt, uint32_t i)
{
  auto cofp = cofactor0( tt, i );
  auto cofn = cofactor1( tt, i );
  bool m=false,n=false;
  uint32_t N = tt.num_bits();
  for ( uint32_t j = 0u; j<N ; j++){
    if(get_bit(cofn, j) > get_bit(cofp, j)){
      m = true ;
    }
    if(get_bit(cofn, j) < get_bit(cofp, j))
    {
      n = true ;
    }
  }
  if( (m && n) ){
    return 0;
  }
  if( n ){
    return -1;
  }
  return 1;
}

} /* namespace kitty */

