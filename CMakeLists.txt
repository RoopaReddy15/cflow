cmake_minimum_required(VERSION 3.13)
project(clang_cfg)

find_package(Clang REQUIRED)

add_executable(clang_cfg parser.cpp)

target_include_directories(clang_cfg PRIVATE ${CLANG_INCLUDE_DIRS})
target_link_libraries(clang_cfg PRIVATE clangTooling clangBasic clangAST)
