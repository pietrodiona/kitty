/* kitty: C++ truth table library
 * Copyright (C) 2017  EPFL
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

#include <gtest/gtest.h>

#include <sstream>

#include <kitty/kitty.hpp>

#include "utility.hpp"

using namespace kitty;

class PrintTest : public kitty::testing::Test
{
protected:
  template<typename TT>
  std::string to_binary( const TT& tt ) const
  {
    std::stringstream ss;
    print_binary( tt, ss );
    return ss.str();
  }
};

TEST_F( PrintTest, print_binary )
{
  EXPECT_EQ( to_binary( from_hex<2>( "8" ) ), "1000" );
  EXPECT_EQ( to_binary( from_hex<3>( "e8" ) ), "11101000" );
  EXPECT_EQ( to_binary( from_hex<7>( "fffefee8fee8e880fee8e880e8808000" ) ), "11111111111111101111111011101000111111101110100011101000100000001111111011101000111010001000000011101000100000001000000000000000" );
}