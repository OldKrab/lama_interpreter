cmake_minimum_required(VERSION 3.14)

set(PROJECT_NAME lama_interpreter)

project(${PROJECT_NAME})

file(GLOB SRC
     "src/*.h"
     "src/*.cpp"
)

add_executable(${PROJECT_NAME} ${SRC})
set(CMAKE_CXX_STANDARD 17)