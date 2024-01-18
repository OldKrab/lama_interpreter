cmake_minimum_required(VERSION 3.14)

project(lama_interpreter C)

add_executable(lama_interpreter src/main.c)
set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -m32 -g -O0 -fstack-protector-all")
target_link_libraries(lama_interpreter ${CMAKE_SOURCE_DIR}/lama/runtime/runtime.a)